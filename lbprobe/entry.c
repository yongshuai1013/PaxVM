/* Freestanding entry for lbprobe, the same hand-rolled
 * crtbegin_dynamic replica paxsvc uses: the guest linker
 * jumps here with the initial stack, and __libc_init (the
 * guest libc's own initializer) takes over, registers the
 * fini array, and calls guest_main as the slingshot.
 * Kept in C so the assembly block stays identical to the
 * proven paxsvc one. */
typedef unsigned int u32;

int guest_main(int argc, char **argv, char **envp);
void __libc_init(unsigned int *elfdata, void (*onexit)(void),
                 int (*slingshot)(int, char **, char **),
                 const void *structors);

__asm__(
    ".text\n"
    ".globl _start\n"
    ".type _start, %function\n"
    "_start:\n"
    "    mov r0, sp\n"
    "    mov r1, #0\n"
    "    adr r2, 0f\n"
    "    adr r3, 1f\n"
    "    b __libc_init\n"
    "0:  b guest_main\n"
    "1:  .long __PREINIT_ARRAY__\n"
    "    .long __INIT_ARRAY__\n"
    "    .long __FINI_ARRAY__\n"
    "    .long __CTOR_LIST__\n");

struct dso_marker { int x; };
__attribute__((section(".data"))) struct dso_marker __dso_handle = {0};

/* The crtbegin arrays the structors table points at, in
 * the era's sentinel form (leading -1, NULL-terminated),
 * byte-identical to what the stock crtbegin emits. The
 * probe defines no static constructors, so all four stay
 * empty; libbinder's own constructors live in its library
 * and are run by the guest linker from its tables. */
__asm__(
    ".section .preinit_array, \"aw\"\n"
    ".globl __PREINIT_ARRAY__\n"
    "__PREINIT_ARRAY__:\n"
    "    .long -1\n"
    "    .long 0\n"
    ".section .init_array, \"aw\"\n"
    ".globl __INIT_ARRAY__\n"
    "__INIT_ARRAY__:\n"
    "    .long -1\n"
    "    .long 0\n"
    ".section .fini_array, \"aw\"\n"
    ".globl __FINI_ARRAY__\n"
    "__FINI_ARRAY__:\n"
    "    .long -1\n"
    "    .long 0\n"
    ".section .ctors, \"aw\"\n"
    ".globl __CTOR_LIST__\n"
    "__CTOR_LIST__:\n"
    "    .long -1\n"
    "    .long 0\n");
