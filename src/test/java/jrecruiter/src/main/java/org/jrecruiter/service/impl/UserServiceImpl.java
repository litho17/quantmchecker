/*
 * Copyright 2006-2014 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.jrecruiter.service.impl;

import java.util.Date;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;

import org.jasypt.digest.StringDigester;
import org.jrecruiter.common.CollectionUtils;
import org.jrecruiter.common.Constants;
import org.jrecruiter.common.Constants.ServerActions;
import org.jrecruiter.common.PasswordGenerator;
import org.jrecruiter.dao.ConfigurationDao;
import org.jrecruiter.dao.RoleDao;
import org.jrecruiter.dao.UserDao;
import org.jrecruiter.model.Role;
import org.jrecruiter.model.ServerSettings;
import org.jrecruiter.model.User;
import org.jrecruiter.model.UserToRole;
import org.jrecruiter.service.NotificationService;
import org.jrecruiter.service.UserService;
import org.jrecruiter.service.exceptions.DuplicateUserException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.MessageSource;
import org.springframework.context.i18n.LocaleContextHolder;
import org.springframework.dao.DataAccessException;
import org.springframework.security.core.userdetails.UserDetails;
import org.springframework.security.core.userdetails.UserDetailsService;
import org.springframework.security.core.userdetails.UsernameNotFoundException;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Propagation;
import org.springframework.transaction.annotation.Transactional;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;

/**
 * Provides user specific services.
 *
 * @author Dorota Puchala
 * @author Gunnar Hillert
 *
 */
@Service("userService")
@Transactional
public class UserServiceImpl implements UserService, UserDetailsService {

	/**
	 *   Initialize Logging.
	 */
	private final static Logger LOGGER = LoggerFactory.getLogger(UserServiceImpl.class);

	private @Autowired NotificationService notificationService;

	private @Autowired ServerSettings serverSettings;

	private @Autowired MessageSource messageSource;

	/**
	 * User Dao.
	 */
	private @Autowired UserDao userDao;

	/**
	 * UserRole Dao.
	 */
	private @Autowired RoleDao roleDao;

	/**
	 * Access to settings.
	 */
	private @Autowired ConfigurationDao configurationDao;

	private @Autowired StringDigester stringDigester;

	//~~~~~Business Methods~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

	/** {@inheritDoc} */
	public User addUser(User user) throws DuplicateUserException{
		if (user == null) {
			throw new IllegalArgumentException("User must not be null.");
		}

		final Date registerDate = new Date();
		user.setRegistrationDate(registerDate);
		user.setUpdateDate(registerDate);
		user.setEnabled(Boolean.FALSE);
		user.setVerificationKey(this.generateUuid());

		if (user.getUsername() == null) {
			user.setUsername(user.getEmail());
		}

		final User duplicateUser = userDao.getUser(user.getUsername());

		if (duplicateUser!= null) {
			throw new DuplicateUserException("User " + duplicateUser.getUsername()
					+ "(Id="  + duplicateUser.getId()
					+ ") already exists!");
		}

		Role role = roleDao.getRole(Constants.Roles.MANAGER.name());

		if (role == null) {
			throw new IllegalStateException("Role was not found but is required.");
		}

		@Bound("1") int i;
		@Inv("= userToRoles c141") final Set<UserToRole> userToRoles = user.getUserToRoles();

		UserToRole utr = new UserToRole();
		utr.setRole(role);
		utr.setUser(user);

		c141: userToRoles.add(utr);

		final User savedUser = userDao.save(user);

		return savedUser;
	}

	/** {@inheritDoc} */
	public User addUser(User user, Boolean verificationRequired) throws DuplicateUserException{

		if (user == null) {
			throw new IllegalArgumentException("User must not be null.");
		}
		if (verificationRequired == null) {
			throw new IllegalArgumentException("verificationRequired must not be null.");
		}

		final Date registerDate = new Date();
		user.setRegistrationDate(registerDate);
		user.setUpdateDate(registerDate);
		user.setEnabled(Boolean.FALSE);
		user.setVerificationKey(this.generateUuid());

		if (user.getUsername() == null) {
			user.setUsername(user.getEmail());
		}

		final User duplicateUser = userDao.getUser(user.getUsername());

		if (duplicateUser!= null) {
			throw new DuplicateUserException("User " + duplicateUser.getUsername()
										   + "(Id="  + duplicateUser.getId()
										   + ") already exists!");
		}

		Role role = roleDao.getRole(Constants.Roles.MANAGER.name());

		if (role == null) {
			throw new IllegalStateException("Role was not found but is required.");
		}

		@Inv("= userToRoles c141") final Set<UserToRole> userToRoles = user.getUserToRoles();

		UserToRole utr = new UserToRole();
		utr.setRole(role);
		utr.setUser(user);

		c141: userToRoles.add(utr);

		final User savedUser = this.saveUser(user);

		if (verificationRequired) {
			@Bound("7") int i;
			@Inv("= context (+ c146 c147 c148)") final Map<String, Object> context = CollectionUtils.getHashMap();
			c146: context.put("user", savedUser);
			c147: context.put("registrationCode", savedUser.getVerificationKey());
			c148: context.put("accountValidationUrl", serverSettings.getServerAddress() + ServerActions.ACCOUNT_VERIFICATION.getPath());

			@Iter("= emailRequest.context context") final EmailRequest emailRequest = new EmailRequest(
					savedUser.getEmail(), messageSource.getMessage("class.UserServiceImpl.addUser.account.validation.subject", null, LocaleContextHolder.getLocale()), context, "account-validation");
			notificationService.sendEmail(emailRequest);
		}
		return savedUser;

	}

	/** {@inheritDoc} */
	public User saveUser(User user) {
		return userDao.save(user);
	}

	/** {@inheritDoc} */
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public User getUser(String username) {
		return userDao.getUser(username);
	}

	/** {@inheritDoc} */
	public void updateUser(User user) {
		Date updateDate = new Date();
		user.setUpdateDate(updateDate);
		userDao.save(user);
	}

	/** {@inheritDoc} */
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public List<User> getAllUsers() {

		return userDao.getAllUsers();
	}

	/** {@inheritDoc} */
	public void deleteUser(User user){
		userDao.remove(user.getId());
	}

	/** {@inheritDoc} */
	public void resetPassword(final User user) {

		final String password = PasswordGenerator.generatePassword();

		user.setPassword(this.stringDigester.digest(password));

		this.updateUser(user);

		@Bound("2") int i;
		@Inv("= context (+ c199 c200)") final Map<String, Object> context = CollectionUtils.getHashMap();
		c199: context.put("user", user);
		c200: context.put("password", password);

		@InvUnk("Unknown API") final EmailRequest emailRequest = new EmailRequest(user.getEmail(),
				   messageSource.getMessage("class.UserServiceImpl.resetPassword.email.subject",
				   null,
				   LocaleContextHolder.getLocale()),
				   context,
				   "get-password");
		this.notificationService.sendEmail(emailRequest);

		LOGGER.info("resetPassword - Email sent to: " + user.getEmail() + "; id: " + user.getId());
	}

	/** {@inheritDoc} */
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public UserDetails loadUserByUsername(final String emailOrUserName) throws UsernameNotFoundException, DataAccessException {

		@InvUnk("Dynamic dispatch") final User user = userDao.getUserByUsernameOrEmail(emailOrUserName.trim());

		if (user==null){
			LOGGER.warn("loadUserByUsername() - No user with id " + emailOrUserName + " found.");
			throw new UsernameNotFoundException("loadUserByUsername() - No user with id " + emailOrUserName + " found.");
		}

		LOGGER.info("User {} ({}) loaded.", new Object[] { user.getUsername(), user.getEmail()});

		return user;
	}

	/** {@inheritDoc} */
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public User getUser(Long userId) {
		return userDao.get(userId);
	}

	/** {@inheritDoc} */
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public List<User> getUsers(Integer pageSize, Integer pageNumber, Map<String, String> sortOrders, Map<String, String> userFilters) {
		return userDao.getUsers(pageSize, pageNumber, sortOrders, userFilters);
	}

	/** {@inheritDoc} */
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public Long getUsersCount() {
		return userDao.getUsersCount();
	}

	public String generateUuid() {
		return UUID.randomUUID().toString();
	}

	/** {@inheritDoc} */
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public User getUserByVerificationKey(final String key) {
		return userDao.getUserByVerificationKey(key);
	}
}
