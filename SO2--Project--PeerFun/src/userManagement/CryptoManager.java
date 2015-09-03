package userManagement;

import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * @author NVH
 * @filename CryptoManager.java
 */
public class CryptoManager {

	public static byte[] computeHash(String x) throws Exception {
		java.security.MessageDigest d = null;
		d = java.security.MessageDigest.getInstance("SHA-1");
		d.reset();
		d.update(x.getBytes());
		return d.digest();
	}

	public static String byteArrayToHexString(byte[] b) {
		StringBuilder sb = new StringBuilder(b.length * 2);
		for (int i = 0; i < b.length; i++) {
			int v = b[i] & 0xff;
			if (v < 16) {
				sb.append('0');
			}
			sb.append(Integer.toHexString(v));
		}
		return sb.toString().toUpperCase();
	}

	public static boolean checkPass(String passWord, User user) {
		String testPassWord = "";
		try {
			testPassWord = byteArrayToHexString(computeHash(passWord));
		} catch (Exception ex) {
			Logger.getLogger(User.class.getName()).log(Level.SEVERE, null, ex);
		}
		
		return testPassWord.equals(user.getHashPassWord());
	}
}
