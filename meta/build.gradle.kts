plugins {
    java
}

repositories {
    mavenCentral()
}

dependencies {
    implementation(files("../../Arend/api/build/libs/api-1.2.0.jar"))
    implementation("org.jetbrains:annotations:19.0.0")
}

configure<JavaPluginConvention> {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

tasks.withType<Wrapper> {
    gradleVersion = "6.2.1"
}
