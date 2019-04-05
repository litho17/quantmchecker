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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import net.jforum.entities.Group;
import net.jforum.entities.User;
import net.jforum.entities.UserSession;
import br.com.caelum.vraptor.Result;
import br.com.caelum.vraptor.ioc.Component;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

/**
 * @author Rafael Steil
 */
@Component
public class GroupInteractionFilter {
	/**
	 * Filter the property bag for forums/show, based on group interaction
	 * settings
	 *
	 * @param userSession the user session of the current logged user
	 */
	public void filterForumListing(Result result, UserSession userSession) {
		@SuppressWarnings("unchecked")

		@InvUnk("Complex loop") Set<UserSession> newSessions = new HashSet<UserSession>();

		for (Group group : userSession.getUser().getGroups()) {
			for (UserSession anotherUserSession : (Collection<UserSession>) result.included().get("onlineUsers")) {
				User user = anotherUserSession.getUser();

				if (user != null && user.getGroups().contains(group)) {
					newSessions.add(anotherUserSession);
				}
			}
		}

		result.include("totalLoggedUsers", newSessions.size());
		result.include("onlineUsers", newSessions);
	}
}
