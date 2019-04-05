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
package net.jforum.core.tags;

import java.io.IOException;
import java.net.URLEncoder;

import javax.servlet.jsp.JspException;

import org.apache.commons.lang.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

/**
 * Given a desired location, builds the link URL
 *
 * @author Rafael Steil
 */
public class URLTag extends JForumTag {

	public static final String URL_ENCODE = "UTF-8";

	private String address;
	private boolean encode;

	/**
	 * @see javax.servlet.jsp.tagext.SimpleTagSupport#doTag()
	 */
	@Override
	public void doTag() throws JspException, IOException {
		@Bound("+ 2 (* 2 address)") int j;
		@Inv("= (- urlBuilder i i) (- (+ c41 c42 c55 c56) c58 c58)") StringBuilder urlBuilder = new StringBuilder(128);
		c41: urlBuilder.append(this.request().getContextPath());

		if (!encode) {
			c42: urlBuilder.append(this.address);
		}
		else {
			if (this.address == null) {
				this.address = "";
			}

			String[] addresses = this.address.split("/");

			@Iter("<= i address") int i = 0;
			String _address;
			for (; i < addresses.length;) {
				_address = addresses[i];
				if (StringUtils.isNotEmpty(_address)) {
					c55: urlBuilder.append("/");
					c56: urlBuilder.append(URLEncoder.encode(_address, URL_ENCODE));
				}
				c58: i = i + 1;
			}
		}

		this.write(this.response().encodeURL(urlBuilder.toString()));
	}

	/**
	 * @param address the resource to set
	 */
	public void setAddress(String address) {
		this.address = address;
	}

	/**
	 * @param encode the encode to set
	 */
	public void setEncode(boolean encode) {
		this.encode = encode;
	}
}
