plugins {
    id("com.android.application")
    id("org.jetbrains.kotlin.android")
}

android {
    namespace = "com.yongshuai.paxvm"
    compileSdk = 34

    defaultConfig {
        applicationId = "com.yongshuai.paxvm"
        minSdk = 26
        targetSdk = 34
        versionCode = 3
        versionName = "0.2.1"
        ndk {
            abiFilters += "arm64-v8a"
        }
    }

    buildTypes {
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
