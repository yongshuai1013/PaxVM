plugins {
    id("com.android.application")
    id("org.jetbrains.kotlin.android")
}

// Pinned signing key (CI secrets): AGP's default debug key is
// generated fresh on every CI runner, so every build used to carry a
// different signature and Android refused overlay installs. When all
// four env vars are present (CI decodes the keystore from secrets),
// builds are signed with the project's permanent key instead; local
// builds without the env vars keep the default debug signature.
val paxvmKeystorePath = System.getenv("PAXVM_KEYSTORE_PATH")
val paxvmKeystorePassword = System.getenv("PAXVM_KEYSTORE_PASSWORD")
val paxvmKeyAlias = System.getenv("PAXVM_KEY_ALIAS")
val paxvmKeyPassword = System.getenv("PAXVM_KEY_PASSWORD")
val usePaxvmSigning = listOf(
    paxvmKeystorePath, paxvmKeystorePassword, paxvmKeyAlias, paxvmKeyPassword
).all { !it.isNullOrBlank() }

android {
    namespace = "com.yongshuai.paxvm"
    compileSdk = 34

    defaultConfig {
        applicationId = "com.yongshuai.paxvm"
        minSdk = 26
        targetSdk = 34
        versionCode = 191
        versionName = "0.9.145"
        ndk {
            abiFilters += "arm64-v8a"
        }
    }

    signingConfigs {
        if (usePaxvmSigning) {
            create("paxvm") {
                storeFile = file(paxvmKeystorePath!!)
                storePassword = paxvmKeystorePassword
                keyAlias = paxvmKeyAlias
                keyPassword = paxvmKeyPassword
            }
        }
    }

    buildTypes {
        debug {
            if (usePaxvmSigning) {
                signingConfig = signingConfigs.getByName("paxvm")
            }
        }
        release {
            isMinifyEnabled = false
        }
    }

    packaging {
        jniLibs {
            // Hard requirement (M0 spec 1.2): the supervisor and guest
            // ship as libsupervisor.so / libguest.so in jniLibs and must
            // land as real files in nativeLibraryDir so the shell can
            // exec them. Without legacy packaging they stay inside the
            // APK and there is no executable path.
            useLegacyPackaging = true
        }
    }

    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_17
        targetCompatibility = JavaVersion.VERSION_17
    }
    kotlinOptions {
        jvmTarget = "17"
    }
}

dependencies {
    // BouncyCastle: HKDF-SHA256 for the ADB pairing cipher in
    // AdbLocal.kt. SPAKE2 itself is implemented there from
    // BoringSSL's spake25519.c (the spake2-java port fails its
    // own key-agreement tests), so no ADB/SPAKE2 library is
    // pulled in.
    implementation("org.bouncycastle:bcprov-jdk18on:1.78.1")
    // Bundled Conscrypt: the ADB pairing needs the TLS
    // exported key material, which the platform
    // Conscrypt cannot serve from an app classloader
    // (0.9.69 field failure); our own provider's
    // sockets + static export call can.
    implementation("org.conscrypt:conscrypt-android:2.5.2")
    testImplementation("junit:junit:4.13.2")
}
