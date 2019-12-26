plugins {
    java
}

repositories {
    mavenCentral()
}

dependencies {
    implementation(files("../../Arend/build/libs/arend-sdk.jar"))
}

configure<JavaPluginConvention> {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

tasks.withType<Wrapper> {
    gradleVersion = "5.5.1"
}
