/*
 * Copyright (c) JForum Team. All rights reserved.
 *
 * The software in this package is published under the terms of the LGPL
 * license a copy of which has been included with this distribution in the
 * license.txt file.
 *
 * The JForum Project
 * http://www.jforum.net
 */
package net.jforum.util;

import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

import net.jforum.core.exceptions.ForumException;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

/**
 * Encodes a string using MD5 hashing
 *
 * @author Rafael Steil
 */
public class MD5 {
	/**
	 * Encodes a string
	 *
	 * @param str String to encode
	 * @return Encoded String
	 * @throws NoSuchAlgorithmException
	 */
	public static String hash(String str) {
		if (str == null || str.length() == 0) {
			throw new IllegalArgumentException("String cannot be null or zero length");
		}

		@Bound("* 2 str") int j;
		@Inv("= (- hexString i i) (- (+ c48 c49 c52) c54 c54)") StringBuilder hexString = new StringBuilder();
		try {
			MessageDigest md = MessageDigest.getInstance("MD5");
			md.update(str.getBytes());
			byte[] hash = md.digest();

			@Iter("<= i str") int i = 0;
			for (; i < hash.length;) {
				byte element = hash[i];
				if ((0xff & element) < 0x10) {
					c48: hexString.append('0');
					c49: hexString.append(Integer.toHexString((0xFF & element)));
				}
				else {
					c52: hexString.append(Integer.toHexString(0xFF & element));
				}
				c54: i = i + 1;
			}
		}
		catch (NoSuchAlgorithmException e) {
			throw new ForumException(e);
		}

		return hexString.toString();
	}
}
