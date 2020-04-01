plugins {
    java
}

repositories {
    mavenCentral()
    maven("https://jitpack.io")
}

dependencies {
    implementation("com.github.JetBrains.Arend:api:master-SNAPSHOT")
    implementation("org.jetbrains:annotations:19.0.0")
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

tasks.withType<Wrapper> {
    gradleVersion = "6.2.1"
}
