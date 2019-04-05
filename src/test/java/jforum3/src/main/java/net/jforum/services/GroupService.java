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
package net.jforum.services;

import java.util.*;

import net.jforum.core.SessionManager;
import net.jforum.core.exceptions.ValidationException;
import net.jforum.entities.Group;
import net.jforum.entities.Role;
import net.jforum.entities.UserSession;
import net.jforum.repository.GroupRepository;
import net.jforum.repository.UserRepository;
import net.jforum.security.RoleManager;
import net.jforum.util.SecurityConstants;

import org.apache.commons.lang.StringUtils;

import br.com.caelum.vraptor.ioc.Component;
import plv.colorado.edu.quantmchecker.qual.*;

/**
 * @author Rafael Steil
 */
@Component
public class GroupService {
	private GroupRepository repository;
	private UserRepository userRepository;
	private UserSession userSession;
	private SessionManager sessionManager;

	public GroupService(GroupRepository repository, UserRepository userRepository,
			UserSession userSession, SessionManager sessionManager) {
		this.repository = repository;
		this.userSession = userSession;
		this.userRepository = userRepository;
		this.sessionManager = sessionManager;
	}

	/**
	 * Save the permissions for this group
	 */
	@SuppressWarnings("unchecked")
	public void savePermissions(int groupId, Map<String, Map<String, List<?>>> myMap) {
		// @Inv("= (+ self it1 it2) (- (+ c85 c88 c91 c94 c97 c109 c112 myMap_init myMap_init) (+ c80 c104))")
		@Inv("and (= (- group.roles it1 it2) (- (+ c85 c88 c91 c94 c97 c109 c112) c80 c104)) (= group.users 0)") Group group = this.repository.get(groupId);

		RoleManager currentRoles = new RoleManager();
		currentRoles.setGroups(Arrays.asList(group));

		group.getRoles().clear();

		boolean isAdministrator = currentRoles.isAdministrator();
		boolean canManageForums = currentRoles.roleExists(SecurityConstants.CAN_MANAGE_FORUMS);
		boolean isCoAdministrator = currentRoles.isCoAdministrator();

		@Bound("+ ary myMap myMap") int j;
		@Inv("= (- groups i) (- c71 c72)") List<Integer> groups = new ArrayList<Integer>();
		int[] ary = currentRoles.getRoleValues(SecurityConstants.GROUPS);
		for (@Iter("<= i ary") int i = 0; i < ary.length;) {
			int gid = ary[i];
			c71: groups.add(gid);
			c72: i = i + 1;
		}

		boolean canInteractwithOtherGroups = currentRoles.roleExists(SecurityConstants.INTERACT_OTHER_GROUPS);
		boolean isSuperAdministrator = this.userSession.getRoleManager().isAdministrator();

		@Iter("<= it1 myMap") Iterator<Map.Entry<String, List<?>>> it1 = myMap.get("boolean").entrySet().iterator();
		while (it1.hasNext()) {
			Map.Entry<String, List<?>> entry;
			c80: entry = it1.next();
			String key = entry.getKey();
			Boolean b = (Boolean)entry.getValue().get(0);

			if (SecurityConstants.ADMINISTRATOR.equals(key)) {
				c85: registerRole(group, key, isSuperAdministrator ? b : isAdministrator);
			}
			else if (SecurityConstants.CAN_MANAGE_FORUMS.equals(key)) {
				c88: registerRole(group, key, isSuperAdministrator ? b : canManageForums);
			}
			else if (SecurityConstants.CO_ADMINISTRATOR.equals(key)) {
				c91: registerRole(group, key, isSuperAdministrator ? b : isCoAdministrator);
			}
			else if (SecurityConstants.INTERACT_OTHER_GROUPS.equals(key)) {
				c94: registerRole(group, key, isSuperAdministrator ? b : canInteractwithOtherGroups);
			}
			else {
				c97: registerRole(group, key, (Boolean)entry.getValue().get(0));
			}
		}

		@Iter("<= it2 myMap") Iterator<Map.Entry<String, List<?>>> it2 = myMap.get("multiple").entrySet().iterator();
		while (it1.hasNext()) {
			Map.Entry<String, List<?>> entry;
			c104: entry = it2.next();
			String key = entry.getKey();

			if (SecurityConstants.GROUPS.equals(key)) {
				c109: registerRole(group, key, isSuperAdministrator ? ((List<Integer>) entry.getValue()) : groups);
			}
			else {
				c112: registerRole(group, key, ((List<Integer>) entry.getValue()));
			}
		}

		this.repository.update(group);

		this.sessionManager.computeAllOnlineModerators();
		//this.userRepository.changeAllowAvatarState(map.getCanHaveProfilePicture(), group);
	}

	/**
	 * Add a new group
	 * @param group
	 */
	public void add(Group group) {
		this.applyCommonConstraints(group);

		if (group.getId() > 0) {
			throw new ValidationException("Cannot save an existing (id > 0) group");
		}

		this.repository.add(group);
	}

	/**
	 * Updates the information of an existing group
	 * @param group
	 */
	public void update(Group group) {
		this.applyCommonConstraints(group);

		if (group.getId() == 0) {
			throw new ValidationException("update() expects a group with an existing id");
		}

		this.repository.update(group);
	}

	/**
	 * Deletes one or more groups
	 * @param ids
	 */
	public void delete(int... ids) {
		if (ids != null) {
			// FIXME: Must not delete a group if it has users
			for (int groupId : ids) {
				Group group = this.repository.get(groupId);
				this.repository.remove(group);
			}
		}
	}

	public void appendRole(Group group, String roleName, int roleValue) {
		for (Role role : group.getRoles()) {
			if (role.getName().equals(roleName)) {
				role.getRoleValues().add(roleValue);
				break;
			}
		}

		this.repository.update(group);
	}

	private void applyCommonConstraints(Group group) {
		if (group == null) {
			throw new NullPointerException("Cannot save a null group");
		}

		if (StringUtils.isEmpty(group.getName())) {
			throw new ValidationException("A group should have a name");
		}
	}

	@Summary({"group.roles", "1"})
	private void registerRole(Group group, String name, List<Integer> values) {
		if (values.size() > 0) {
			group.addRole(this.createRole(name, values));
		}
	}

	@Summary({"group.roles", "1"})
	private void registerRole(Group group, String name, boolean isAllowed) {
		if (isAllowed) {
			group.addRole(this.createRole(name, null));
		}
	}

	private Role createRole(String name, List<Integer> values) {
		@Bound("values") int i;
		@Inv("(and (= (- role.roleValues it) (- c210 c209)) (= role.group.roles 0) (= role.group.users 0))") Role role = new Role();
		role.setName(name);

		if (values != null) {
			@Iter("<= it values") Iterator<Integer> it = values.iterator();
			int value;
			while (it.hasNext()) {
				c209: value = it.next();
				c210: role.addRoleValue(value);
			}
		}

		return role;
	}
}
