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

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

public class URLBuilder {
	/**
	 * Builds an URL by adding a '/' between each argument, and ".page" in the end
	 * @param args The parts of the URL to build
	 * @return the URL
	 */
	public static String build(Object... args) {
		@Bound("+ 2 (* 2 args)") int j;
		@Inv("= (- sb i i) (- (+ c24 c27 c28 c31) c29 c29)") StringBuilder sb = new StringBuilder();
		c24: sb.append('/');

		@Iter("<= i args") int i = 0;
		for (;i < args.length - 1;) {
			c27: sb.append(args[i]);
			c28: sb.append('/');
			c29: i = i + 1;
		}

		c31: sb.append(args[args.length - 1]);

		return sb.toString();
	}
}
