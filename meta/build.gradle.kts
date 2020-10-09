val projectArend = gradle.includedBuild("Arend")

plugins {
    java
}

task<JavaExec>("cliCheck") {
    group = "verification"
    dependsOn(projectArend.task(":cli:jarDep"), tasks["classes"])
    main = "-jar"
    val jarDepPath = projectArend.projectDir.resolve("cli/build/libs/cli-1.5.0-full.jar").absolutePath
    args(jarDepPath, "-tcr")
    workingDir(projectDir.parent)
}

task("copyJarDep") {
    dependsOn(projectArend.task(":cli:copyJarDep"))
}

repositories {
    mavenCentral()
}

dependencies {
    implementation("org.arend:api")
}

java {
    sourceCompatibility = JavaVersion.VERSION_11
    targetCompatibility = JavaVersion.VERSION_11
}

tasks.withType<Wrapper> {
    gradleVersion = "6.5"
}

tasks.withType<JavaCompile> {
    options.encoding = "UTF-8"
}
