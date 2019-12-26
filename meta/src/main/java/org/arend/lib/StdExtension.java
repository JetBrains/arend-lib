package org.arend.lib;

import org.arend.ext.ArendExtension;

@SuppressWarnings("unused")
public class StdExtension implements ArendExtension {
    @Override
    public void initialize() {
        System.out.println("Hello World!");
    }
}
