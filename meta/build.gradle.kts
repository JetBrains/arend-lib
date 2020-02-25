plugins {
    java
}

repositories {
    mavenCentral()
}

dependencies {
    implementation(files("../../Arend/build/libs/arend-api-1.2.0.jar"))
    implementation("com.google.code.findbugs:jsr305:3.0.2")
}

configure<JavaPluginConvention> {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

tasks.withType<Wrapper> {
    gradleVersion = "5.5.1"
}
