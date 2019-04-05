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
package net.jforum.formatters;

import java.util.ArrayList;
import java.util.List;

import net.jforum.util.ConfigKeys;
import net.jforum.util.JForumConfig;
import br.com.caelum.vraptor.ioc.ApplicationScoped;
import br.com.caelum.vraptor.ioc.Component;
import br.com.caelum.vraptor.ioc.Container;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

/**
 * @author Rafael Steil
 */
@Component
@ApplicationScoped
public class PostFormatters extends ArrayList<Formatter> {
	public PostFormatters(JForumConfig config, Container container) throws Exception {
		@Bound("config") int j;
		String value = config.getValue(ConfigKeys.MESSAGE_FORMATTERS);
		@Inv("= (- formatters i) (- c90 c91)") List<String> formatters = new ArrayList<String>();
		if (value != null) {
			String[] parts = value.split(",");

			@Iter("<= i config") int i = 0;
			for (; i < parts.length;) {
				String p = parts[i];
				c90: formatters.add(p.trim());
				c91: i++;
			}
		}

		for (String name : formatters) {
			Class<? extends Formatter> k = (Class<? extends Formatter>)Class.forName(name);
			add(container.instanceFor(k));
		}
	}
}
