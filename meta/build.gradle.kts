val projectArend = gradle.includedBuild("Arend")

plugins {
    java
}

tasks.register<JavaExec>("cliCheck") {
    group = "verification"
    dependsOn(projectArend.task(":cli:jarDep"), tasks.named("classes"))
    main = "-jar"
    val jarDepPath = projectArend.projectDir.resolve("cli/build/libs/cli-1.6.0-full.jar").absolutePath
    args(jarDepPath, "-tcr")
    workingDir(projectDir.parent)
}

tasks.register("copyJarDep") {
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

tasks.withType<Wrapper>().configureEach {
    gradleVersion = "6.7"
}

tasks.compileJava {
    options.encoding = "UTF-8"
}
