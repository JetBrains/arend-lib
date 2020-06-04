val projectArend = gradle.includedBuild("Arend")

plugins {
    java
}

task<JavaExec>("cliCheck") {
    group = "verification"
    dependsOn(projectArend.task(":cli:jarDep"), tasks["classes"])
    main = "-jar"
    val jarDepPath = projectArend.projectDir.resolve("cli/build/libs/cli-1.3.0-full.jar").absolutePath
    args(jarDepPath, "-tcr")
    workingDir(projectDir.parent)
}

repositories {
    mavenCentral()
}

dependencies {
    implementation("org.arend:api")
    implementation("org.jetbrains:annotations:19.0.0")
}

java {
    sourceCompatibility = JavaVersion.VERSION_11
    targetCompatibility = JavaVersion.VERSION_11
}

tasks.withType<Wrapper> {
    gradleVersion = "6.3"
}
