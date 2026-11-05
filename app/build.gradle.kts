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
        versionCode = 4
        versionName = "0.2.2"
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
