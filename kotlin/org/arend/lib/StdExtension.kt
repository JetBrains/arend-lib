package org.arend.lib

import org.arend.ext.ArendExtension

@Suppress("unused")
class StdExtension : ArendExtension {
    override fun initialize() {
        println("Hello World!")
    }
}