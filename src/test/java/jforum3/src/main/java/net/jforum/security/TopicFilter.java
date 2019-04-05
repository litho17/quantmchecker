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
package net.jforum.security;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.jforum.entities.Topic;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

/**
 * Given a list of topics and a rolemanager, filter the topics based on the security roles
 * @author Rafael Steil
 */
public class TopicFilter {
	public List<Topic> filter(List<Topic> topics, RoleManager roleManager) {
		@Bound("topics") int i;
		@Inv("= (- result it) (- c34 c32)") List<Topic> result = new ArrayList<Topic>();

		if (roleManager != null) {
			@Iter("<= it topics") Iterator<Topic> it = topics.iterator();
			while (it.hasNext()) {
				Topic topic;
				c32: topic = it.next();
				if (roleManager.isForumAllowed(topic.getForum().getId())) {
					c34: result.add(topic);
				}
			}
		}

		return result;
	}
}
