package utils;

import org.junit.Test;

import static org.fest.assertions.Assertions.assertThat;

public class ObfuscateTest {

    @Test
    public void testObfuscate() {
        String string = "BiberIsDeMax";

        String obfuscated = Obfuscate.obfuscate(string);

        assertThat("OvoreVfQrZnk".equals(obfuscated));
    }


    @Test
    public void testDeObfuscate() {
        String string = "OvoreVfQrZnk";

        String deObfuscated = Obfuscate.deObfuscate(string);

        assertThat("BiberIsDeMax".equals(deObfuscated));
    }

    @Test
    public void testBoth() {
        String string = "BiberIsDeMax";

        String obfuscated = Obfuscate.obfuscate(string);
        String deObfuscated = Obfuscate.deObfuscate(string);

        assertThat("BiberIsDeMax".equals(deObfuscated));
    }
}
