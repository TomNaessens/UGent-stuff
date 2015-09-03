package ods.lab2.utils;

import org.eclipse.persistence.internal.oxm.conversion.Base64;

public class Base64Decoder {

	public static String decode(String string) {
		byte[] decoded = Base64.base64Decode(string.getBytes());
		return new String(decoded);
	}
	
}
