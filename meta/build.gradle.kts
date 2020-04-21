plugins {
    java
}

repositories {
    mavenCentral()
}

dependencies {
    implementation(files("../../Arend/api/build/libs/api-1.3.0.jar"))
    implementation("org.jetbrains:annotations:19.0.0")
}

java {
    sourceCompatibility = JavaVersion.VERSION_11
    targetCompatibility = JavaVersion.VERSION_11
}

tasks.withType<Wrapper> {
    gradleVersion = "6.3"
}
