val projectArend = gradle.includedBuild("Arend")

plugins {
    java
}

tasks.register<JavaExec>("cliCheck") {
    group = "verification"
    dependsOn(projectArend.task(":cli:jarDep"), tasks.named("classes"))
    mainClass.set("-jar")
    val jarDepPath = projectArend.projectDir.resolve("cli/build/libs/cli-1.10.0-full.jar").absolutePath
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
    sourceCompatibility = JavaVersion.VERSION_17
    targetCompatibility = JavaVersion.VERSION_17
}

tasks.withType<Wrapper>().configureEach {
    gradleVersion = "8.5"
}

tasks.compileJava {
    options.encoding = "UTF-8"
}
