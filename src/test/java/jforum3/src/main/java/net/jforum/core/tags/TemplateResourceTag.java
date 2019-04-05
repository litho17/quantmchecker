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

import net.jforum.util.ConfigKeys;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

/**
 * Given a resource name, builds it's absolute URL, to be used in the templates
 * @author Rafael Steil
 */
public class TemplateResourceTag extends JForumTag {
	private String item;

	/**
	 * @see javax.servlet.jsp.tagext.SimpleTagSupport#doTag()
	 */
	@Override
	public void doTag() throws IOException {
		@Bound("3") int i;
		@Inv("= sb (+ c32 c33 c34)") StringBuilder sb = new StringBuilder(128);

		c32: sb.append(this.request().getContextPath());
		c33: sb.append(config().getValue(ConfigKeys.TEMPLATE_DIRECTORY));
		c34: sb.append(this.item);

		String path = sb.toString();
		this.write(path);
	}

	/**
	 * @param item the resource to set
	 */
	public void setItem(String item) {
		this.item = item;
	}
}
