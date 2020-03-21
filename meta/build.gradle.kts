plugins {
    java
}

repositories {
    mavenCentral()
    mavenLocal()
}

dependencies {
    val arendVersion = "1.2.0"
    implementation("org.arend:api:$arendVersion")
    implementation("org.jetbrains:annotations:19.0.0")

    testImplementation("org.arend:base:$arendVersion")
    testImplementation("org.arend:cli:$arendVersion")
    testImplementation("org.arend:tester:$arendVersion")
    testImplementation("junit:junit:4.12")
    testImplementation("org.hamcrest:hamcrest-library:1.3")
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

tasks.withType<Wrapper> {
    gradleVersion = "6.2.1"
}
