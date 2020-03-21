package org.arend.lib;

import org.arend.typechecking.TypeCheckingTestCase;
import org.junit.Test;

public class SampleTest extends TypeCheckingTestCase {
    @Test
    public void simple() {
        typeCheckDef("\\func id {A : \\Type} (a : A) => a");
    }
}
