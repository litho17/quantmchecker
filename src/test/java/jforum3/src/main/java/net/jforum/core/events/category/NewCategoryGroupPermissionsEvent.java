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
package net.jforum.core.events.category;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.jforum.entities.Category;
import net.jforum.entities.Group;
import net.jforum.entities.UserSession;
import net.jforum.events.EmptyCategoryEvent;
import net.jforum.repository.GroupRepository;
import net.jforum.services.GroupService;
import net.jforum.util.SecurityConstants;
import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;

/**
 * @author Rafael Steil
 */
public class NewCategoryGroupPermissionsEvent extends EmptyCategoryEvent {
	private GroupRepository groupRepository;
	private GroupService groupService;
	private final UserSession userSession;

	public NewCategoryGroupPermissionsEvent(GroupRepository groupRepository, GroupService groupService,
		UserSession userSession) {
		this.groupRepository = groupRepository;
		this.groupService = groupService;
		this.userSession = userSession;
	}

	/**
	 * When a new category is added, set group access automatically.
	 * Every group which is an Administrator and every user group which is
	 * Co Administrator will have access by default to the new category.
	 * @see net.jforum.events.EmptyCategoryEvent#added(net.jforum.entities.Category)
	 */
	@Override
	public void added(Category category) {
		@InvUnk("Unknown API") List<Group> allGroups = this.groupRepository.getAllGroups();
		@Inv("= (- processedGroups it) (- c58 c56)") List<Group> processedGroups = new ArrayList<Group>();

		@Iter("<= it userGroups") Iterator<Group> it = this.userSession.user.groups.iterator();
		while (it.hasNext()) {
			Group group;
			c56: group = it.next();
			if (this.isGoodCandidate(group)) {
				c58: processedGroups.add(group);
				this.groupService.appendRole(group, SecurityConstants.CATEGORY, category.getId());
			}
		}

		for (Group group : allGroups) {
			if (!processedGroups.contains(group) && group.roleExist(SecurityConstants.ADMINISTRATOR)) {
				this.groupService.appendRole(group, SecurityConstants.CATEGORY, category.getId());
			}
		}
	}

	private boolean isGoodCandidate(Group group) {
		return group.roleExist(SecurityConstants.ADMINISTRATOR)
			|| group.roleExist(SecurityConstants.CO_ADMINISTRATOR);
	}
}
