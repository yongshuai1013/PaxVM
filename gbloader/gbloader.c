/*
 * gbloader -- manual ELF loader for PaxVM dynamic guests (S4).
 *
 * Why this exists: a dynamic guest binary names its interpreter
 * by absolute guest path (/system/bin/linker). The host kernel
 * cannot resolve that path, and Gingerbread's bionic linker has
 * no "linker <program> <args>" standalone mode -- it trusts the
 * kernel-supplied auxv (AT_PHDR/AT_ENTRY describe the main
 * program). So the supervisor rewrites a dynamic execve into an
 * exec of THIS loader, with a rebuilt argv:
 *
 *   loader argv: [0]=target guest path
 *                [1]=program argv[0]
 *                [2..]=program argv[1..]
 *   loader envp: the program's environment, untouched.
 *
 * The loader (running as an ordinary traced compat process; all
 * its path syscalls are translated by the supervisor) maps the
 * target and its PT_INTERP linker by hand, builds a
 * kernel-faithful initial stack (argc/argv/envp/auxv), and jumps
 * to the linker's _start with r0 = sp, exactly as the kernel
 * would have arranged (see bionic237/linker/arch/arm/begin.S).
 *
 * Built as a 32-bit ARM fully static binary linked at a high
 * text address (0x40000000): static so the kernel loads it
 * directly with no interpreter of its own, high so its own
 * image never collides with the target's fixed low load
 * addresses (ET_EXEC at 0x8000). (The Bootlin GCC ignores
 * -static-pie and emits a dynamic PIE; the fixed high address
 * achieves the same separation deterministically.)
 */
#define _GNU_SOURCE
#include <elf.h>
#include <fcntl.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <unistd.h>

extern char **environ;

#define PAGE_MASK (~(uintptr_t)0xfff)
#define PAGE_UP(x) (((x) + 0xfff) & PAGE_MASK)

static void say(const char *s) { (void)!write(2, s, strlen(s)); }

/* A guest service's stderr is /dev/null, so a loader error
 * would vanish. Mirror it into a capture file at the guest
 * root (the supervisor translates the path; the shell dumps
 * the file at session end, like the init kmsg capture). */
static void log_to_file(const char *what, const char *path) {
    int fd = open("/.gbloader-err", O_WRONLY | O_CREAT | O_APPEND, 0666);
    if (fd < 0)
        return;
    (void)!write(fd, "gbloader: ", 10);
    (void)!write(fd, what, strlen(what));
    if (path) {
        (void)!write(fd, ": ", 2);
        (void)!write(fd, path, strlen(path));
    }
    (void)!write(fd, "\n", 1);
    close(fd);
}

static void die(const char *what, const char *path) {
    say("gbloader: ");
    say(what);
    if (path) {
        say(": ");
        say(path);
    }
    say("\n");
    log_to_file(what, path);
    _exit(127);
}

/* The Gingerbread linker does not relocate itself: it runs
 * correctly only because on a real device the kernel maps its
 * first page at 0xb0000000: the address its ELF header and
 * program headers were linked to live at. Map that page from
 * the linker file
 * itself, read-only, at the linker's linked home. This is the
 * one piece of the kernel's interp loading that the generic
 * segment walk cannot express (the first LOAD is a dummy with
 * vaddr 0 / memsz 0 pointing at this page via its paddr). */
static void map_linker_header_page(const char *path, uintptr_t base) {
    int fd = open(path, O_RDONLY);
    if (fd < 0)
        die("header page open", path);
    void *m = mmap((void *)base, 0x1000, PROT_READ,
                   MAP_FIXED | MAP_PRIVATE, fd, 0);
    close(fd);
    if (m != (void *)base)
        die("header page map", path);
}

struct image {
    uintptr_t bias;      /* load bias (0 for ET_EXEC) */
    uintptr_t entry;     /* absolute entry point */
    uintptr_t phdr;      /* absolute address of phdr table, or 0 */
    uintptr_t hdr_addr;  /* where the ELF header page must live
                          * (the GB linker's dummy LOAD carries it
                          * in its paddr: 0xb0000000), or 0 */
    uintptr_t load_base; /* the image's effective base, for
                          * AT_BASE: hdr_addr when present, else
                          * the reservation start */
    uint32_t phnum;
    char interp[128];    /* PT_INTERP string, "" when none */
};

static Elf32_Phdr g_ph[64];

/* Load one ELF32 image from `path`. All segment mmaps use
 * MAP_FIXED over a PROT_NONE reservation of the whole span, so
 * the layout is exact and bss tails are handled explicitly. */
static void load_image(const char *path, struct image *img) {
    int fd = open(path, O_RDONLY);
    if (fd < 0)
        die("open failed", path);
    Elf32_Ehdr eh;
    if (read(fd, &eh, sizeof eh) != (ssize_t)sizeof eh)
        die("short ehdr", path);
    if (memcmp(eh.e_ident, ELFMAG, SELFMAG) != 0 || eh.e_ident[EI_CLASS] != ELFCLASS32 ||
        eh.e_machine != EM_ARM)
        die("not an ELF32/ARM file", path);
    if (eh.e_phnum > 64)
        die("too many phdrs", path);
    if (lseek(fd, (off_t)eh.e_phoff, SEEK_SET) < 0)
        die("lseek phdr", path);
    size_t phbytes = (size_t)eh.e_phnum * sizeof(Elf32_Phdr);
    if (read(fd, g_ph, phbytes) != (ssize_t)phbytes)
        die("short phdr", path);

    img->interp[0] = 0;
    img->hdr_addr = 0;
    uintptr_t lo = ~(uintptr_t)0, hi = 0;
    uint32_t i;
    for (i = 0; i < eh.e_phnum; i++) {
        Elf32_Phdr *p = &g_ph[i];
        if (p->p_type == PT_INTERP) {
            size_t n = p->p_filesz < sizeof img->interp - 1 ? p->p_filesz : sizeof img->interp - 1;
            if (lseek(fd, (off_t)p->p_offset, SEEK_SET) >= 0 && read(fd, img->interp, n) > 0)
                img->interp[n] = 0;
            else
                die("short interp", path);
        }
        if (p->p_type == PT_LOAD && p->p_memsz == 0 && p->p_filesz == 0 &&
            p->p_paddr != 0) {
            /* Dummy header segment: its paddr names the address
             * the ELF header page is linked to live at. */
            img->hdr_addr = p->p_paddr;
        }
        if (p->p_type == PT_LOAD && p->p_memsz > 0) {
            /* Zero-memsz segments occupy nothing and must not
             * poison the span: the Gingerbread linker carries a
             * dummy LOAD at vaddr 0 with memsz 0, which otherwise
             * stretches the reservation to ~3 GB from address 0
             * and makes it fail outright. */
            if (p->p_vaddr < lo)
                lo = p->p_vaddr;
            if (p->p_vaddr + p->p_memsz > hi)
                hi = p->p_vaddr + p->p_memsz;
        }
    }
    if (hi == 0)
        die("no PT_LOAD", path);
    lo &= PAGE_MASK;

    uintptr_t base;
    if (eh.e_type == ET_EXEC) {
        base = 0;
        void *r = mmap((void *)lo, hi - lo, PROT_NONE,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
        if (r != (void *)lo)
            die("reserve exec range", path);
    } else {
        void *r = mmap(0, hi - lo, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (r == MAP_FAILED)
            die("reserve dyn range", path);
        base = (uintptr_t)r - lo;
    }
    img->bias = base;

    img->phdr = 0;
    for (i = 0; i < eh.e_phnum; i++) {
        Elf32_Phdr *p = &g_ph[i];
        if (p->p_type == PT_PHDR)
            img->phdr = base + p->p_vaddr;
        if (p->p_type != PT_LOAD || p->p_memsz == 0)
            continue;
        int prot = ((p->p_flags & PF_R) ? PROT_READ : 0) |
                   ((p->p_flags & PF_W) ? PROT_WRITE : 0) |
                   ((p->p_flags & PF_X) ? PROT_EXEC : 0);
        uintptr_t seg = base + p->p_vaddr;
        uintptr_t seg_pg = seg & PAGE_MASK;
        size_t file_len = (size_t)(p->p_filesz + (seg - seg_pg));
        if (file_len > 0) {
            void *m = mmap((void *)seg_pg, file_len, prot,
                           MAP_FIXED | MAP_PRIVATE, fd,
                           (off_t)(p->p_offset & PAGE_MASK));
            if (m == MAP_FAILED)
                die("map segment", path);
        }
        /* Anonymous tail for memsz > filesz beyond the last file
         * page. The partial page at filesz end is already
         * zero-filled by the file mapping itself. */
        uintptr_t fend = PAGE_UP(seg + p->p_filesz);
        uintptr_t mend = PAGE_UP(seg + p->p_memsz);
        if (mend > fend) {
            void *m = mmap((void *)fend, mend - fend, prot,
                           MAP_FIXED | MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
            if (m == MAP_FAILED)
                die("map bss", path);
        }
    }
    if (img->phdr == 0) {
        /* Fall back to e_phoff when it lands inside a segment. */
        for (i = 0; i < eh.e_phnum; i++) {
            Elf32_Phdr *p = &g_ph[i];
            if (p->p_type == PT_LOAD && eh.e_phoff >= p->p_offset &&
                eh.e_phoff < p->p_offset + p->p_filesz) {
                img->phdr = base + p->p_vaddr + (eh.e_phoff - p->p_offset);
                break;
            }
        }
    }
    img->entry = base + eh.e_entry;
    img->load_base = img->hdr_addr != 0 ? img->hdr_addr : base + lo;
    img->phnum = eh.e_phnum;
    close(fd);
}

static struct image g_target, g_linker;

/* The initial stack image, built on a fresh 8 MiB mapping:
 * strings at the top, then [argc][argv..][NULL][envp..][NULL]
 * [auxv pairs][AT_NULL pair], 16-byte aligned, exactly the
 * layout the kernel hands to an interpreter. */
__attribute__((noreturn)) static void launch(int pargc, char **pargv) {
    const size_t stack_sz = 8u << 20;
    char *stk = mmap(0, stack_sz, PROT_READ | PROT_WRITE,
                     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (stk == MAP_FAILED)
        die("stack mmap", 0);
    uintptr_t top = (uintptr_t)stk + stack_sz;

    /* Copy the strings (program argv, environment) to the top of
     * the new stack, recording their new addresses. */
    int envc = 0;
    while (environ[envc])
        envc++;
    static uintptr_t s_arg[128];
    static uintptr_t s_env[512];
    if (pargc > 128 || envc > 512)
        die("argv/env too large", 0);
    uintptr_t cur = top;
    int i;
    for (i = pargc - 1; i >= 0; i--) {
        size_t n = strlen(pargv[i]) + 1;
        cur -= n;
        memcpy((void *)cur, pargv[i], n);
        s_arg[i] = cur;
    }
    for (i = envc - 1; i >= 0; i--) {
        size_t n = strlen(environ[i]) + 1;
        cur -= n;
        memcpy((void *)cur, environ[i], n);
        s_env[i] = cur;
    }
    /* 16 random bytes for AT_RANDOM. */
    cur -= 16;
    uintptr_t random_ptr = cur;
    {
        unsigned seed = (unsigned)getpid() * 2654435761u ^ (unsigned)(uintptr_t)stk;
        uint32_t *r = (uint32_t *)cur;
        for (i = 0; i < 4; i++) {
            seed = seed * 1103515245u + 12345u;
            r[i] = seed;
        }
    }

    /* auxv pairs: the set the kernel supplies for an interp'd
     * program. The Gingerbread linker reads PHDR/PHENT(implicit)/
     * PHNUM/ENTRY; the rest is kernel-faithful completeness. */
    struct {
        uint32_t type, val;
    } aux[] = {
        {AT_PHDR, (uint32_t)g_target.phdr},
        {AT_PHENT, (uint32_t)sizeof(Elf32_Phdr)},
        {AT_PHNUM, g_target.phnum},
        {AT_ENTRY, (uint32_t)g_target.entry},
        {AT_BASE, (uint32_t)g_linker.load_base},
        {AT_UID, (uint32_t)getuid()},
        {AT_EUID, (uint32_t)geteuid()},
        {AT_GID, (uint32_t)getgid()},
        {AT_EGID, (uint32_t)getegid()},
        {AT_PAGESZ, 4096},
        {AT_HWCAP, 0},
        {AT_RANDOM, (uint32_t)random_ptr},
        {AT_SECURE, 0},
        {AT_NULL, 0},
    };
    const int naux = (int)(sizeof aux / sizeof aux[0]);

    size_t words = 1 + (size_t)pargc + 1 + (size_t)envc + 1 + (size_t)naux * 2;
    cur &= ~(uintptr_t)0xf;
    cur -= words * 4;
    cur &= ~(uintptr_t)0xf;
    uint32_t *sp = (uint32_t *)cur;
    uint32_t *w = sp;
    *w++ = (uint32_t)pargc;
    for (i = 0; i < pargc; i++)
        *w++ = (uint32_t)s_arg[i];
    *w++ = 0;
    for (i = 0; i < envc; i++)
        *w++ = (uint32_t)s_env[i];
    *w++ = 0;
    for (i = 0; i < naux; i++) {
        *w++ = aux[i].type;
        *w++ = aux[i].val;
    }

    uintptr_t entry = g_linker.entry;
    __asm__ volatile(
        "mov sp, %0\n"
        "mov r0, %0\n"
        "mov r1, #0\n"
        "bx %1\n"
        :
        : "r"(sp), "r"(entry)
        : "memory");
    __builtin_unreachable();
}

int main(int argc, char **argv) {
    if (argc < 1)
        _exit(127);
    const char *target = argv[0];
    load_image(target, &g_target);
    if (g_target.interp[0] == 0)
        die("target has no PT_INTERP", target);
    load_image(g_target.interp, &g_linker);
    /* Place the linker's own header page where it was linked
     * to live (0xb0000000, from the dummy LOAD's paddr), so the
     * headers the linker reads about itself sit exactly where
     * a real kernel puts them. */
    if (g_linker.hdr_addr != 0)
        map_linker_header_page(g_target.interp, g_linker.hdr_addr);

    char **pargv = argv + 1;
    int pargc = argc - 1;
    if (pargc == 0) {
        /* No program argv was handed over: use the target path
         * itself as argv[0]. */
        pargv = argv;
        pargc = 1;
    }
    launch(pargc, pargv);
}
