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
package org.jrecruiter.model;

import java.util.*;

import javax.persistence.CascadeType;
import javax.persistence.Column;
import javax.persistence.Entity;
import javax.persistence.FetchType;
import javax.persistence.OneToMany;
import javax.persistence.Table;
import javax.persistence.Temporal;
import javax.persistence.TemporalType;
import javax.persistence.Transient;
import javax.persistence.UniqueConstraint;
import javax.validation.constraints.NotNull;
import javax.validation.constraints.Size;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlID;
import javax.xml.bind.annotation.XmlTransient;
import javax.xml.bind.annotation.adapters.XmlJavaTypeAdapter;

import org.hibernate.annotations.Parameter;
import org.hibernate.annotations.Type;
import org.hibernate.validator.constraints.Email;
import org.jrecruiter.common.Constants.UserAuthenticationType;
import org.springframework.security.core.GrantedAuthority;
import org.springframework.security.core.userdetails.UserDetails;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

/**
 * This class represents a user.
 *
 * @author  Gunnar Hillert
 */
@XmlAccessorType(XmlAccessType.FIELD)
@Entity
@Table(uniqueConstraints = { @UniqueConstraint( columnNames = { "email" } ),
		@UniqueConstraint( columnNames = { "username" } ) }
)
public class User extends BaseModelObject implements UserDetails {

	/**
	 * serialVersionUID.
	 */
	private static final long serialVersionUID = -1530641858689315559L;

	//~~~~~Fields~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

	@XmlID
	@NotNull
	@Size(min=5, max=50)
	@Column(unique=true)
	private String username;

	@NotNull
	@Size(max=120)
	private String password;

	@NotNull
	@Size(max=50)
	private String firstName;

	@NotNull
	@Size(max=50)
	private String lastName;

	@Size(max=50)
	@Column(unique=false, nullable=true, insertable=true,
	updatable=true, length=50)
	private String company;

	@Size(max=25)
	private String phone;

	@Size(max=25)
	private String fax;

	@Size(max=50)
	@Email
	private String email;

	@XmlAttribute
	@XmlJavaTypeAdapter(JaxbDateAdapter.class)
	@Temporal(TemporalType.TIMESTAMP)
	private Date registrationDate;

	@XmlAttribute
	@XmlJavaTypeAdapter(JaxbDateAdapter.class)
	private Date updateDate;

	@XmlAttribute
	@XmlJavaTypeAdapter(JaxbDateAdapter.class)
	@Temporal(TemporalType.TIMESTAMP)
	private Date lastLoginDate;

	@XmlTransient
	@OneToMany(cascade={CascadeType.ALL}, fetch=FetchType.LAZY, mappedBy="user", targetEntity = Job.class)
	private Set<Job> jobs = new HashSet<Job>(0);

	@XmlElement(name="roles")
	@OneToMany(cascade={CascadeType.ALL}, fetch=FetchType.LAZY, mappedBy="user")
	public Set<UserToRole> userToRoles = new HashSet<UserToRole>(0);

	@XmlAttribute
	private Boolean enabled  = Boolean.FALSE;

	@Size(max=36)
	@Column(unique=true)
	private String  verificationKey;

	@Type(type = "org.jrecruiter.common.GenericEnumUserType", parameters = {
			@Parameter(name = "enumClass", value = "org.jrecruiter.common.Constants$UserAuthenticationType"),
			@Parameter(name = "identifierMethod", value = "getId"),
			@Parameter(name = "valueOfMethod", value = "fromId") })
	@NotNull
	private UserAuthenticationType userAuthenticationType = UserAuthenticationType.USERNAME_PASSWORD;

	// Constructors

	/** default constructor */
	public User() {
	}

	/** minimal constructor */
	public User(Long id, String username, String password, String firstName,
			String lastName, String email, Date registerDate) {
		this.id = id;
		this.username = username;
		this.password = password;
		this.firstName = firstName;
		this.lastName = lastName;
		this.email = email;
		this.registrationDate = registerDate;
	}
	/** full constructor */
	public User(Long id, String username, String password, String firstName,
			String lastName, String company, String phone, String fax,
			String email, Date registerDate,
			Date updateDate, Set<Job> jobs,
			Set<UserToRole> userToRoles) {
		this.id = id;
		this.username = username;
		this.password = password;
		this.firstName = firstName;
		this.lastName = lastName;
		this.company = company;
		this.phone = phone;
		this.fax = fax;
		this.email = email;
		this.registrationDate = registerDate;
		this.updateDate = updateDate;
		this.jobs = jobs;
		this.userToRoles = userToRoles;
	}

	public String getUsername() {
		return this.username;
	}

	public void setUsername(String username) {
		this.username = username;
	}

	public String getPassword() {
		return this.password;
	}

	public void setPassword(String password) {
		this.password = password;
	}

	public String getFirstName() {
		return this.firstName;
	}

	public void setFirstName(String firstName) {
		this.firstName = firstName;
	}

	public String getLastName() {
		return this.lastName;
	}

	public void setLastName(String lastName) {
		this.lastName = lastName;
	}

	public String getCompany() {
		return this.company;
	}

	public void setCompany(String company) {
		this.company = company;
	}

	public String getPhone() {
		return this.phone;
	}

	public void setPhone(String phone) {
		this.phone = phone;
	}

	public String getFax() {
		return this.fax;
	}

	public void setFax(String fax) {
		this.fax = fax;
	}

	public String getEmail() {
		return this.email;
	}

	public void setEmail(String email) {
		this.email = email;
	}

	public Date getRegistrationDate() {
		return this.registrationDate;
	}

	public void setRegistrationDate(Date registrationDate) {
		this.registrationDate = registrationDate;
	}

	public Date getUpdateDate() {
		return this.updateDate;
	}

	public void setUpdateDate(Date updateDate) {
		this.updateDate = updateDate;
	}

	public Set<Job> getJobs() {
		return this.jobs;
	}

	public void setJobs(Set<Job> jobs) {
		this.jobs = jobs;
	}

	public Set<UserToRole> getUserToRoles() {
		return this.userToRoles;
	}

	public void setUserToRoles(Set<UserToRole> userToRoles) {
		this.userToRoles = userToRoles;
	}

	public UserAuthenticationType getUserAuthenticationType() {
		return userAuthenticationType;
	}

	public void setUserAuthenticationType(
			UserAuthenticationType userAuthenticationType) {
		this.userAuthenticationType = userAuthenticationType;
	}

	//~~~~~~~~ Implemented from Spring Security ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
	/**
	 * @see org.acegisecurity.userdetails.UserDetails#isAccountNonExpired()
	 * @return Returns the accountNonExpired.
	 */
	@Transient
	public boolean isAccountNonExpired() {
		return true;
	}

	/**
	 * @see org.acegisecurity.userdetails.UserDetails#isAccountNonLocked()
	 * @return Returns the accountNonLocked.
	 */
	@Transient
	public boolean isAccountNonLocked() {
		return true;
	}

	/**
	 * @see org.acegisecurity.userdetails.UserDetails#isCredentialsNonExpired()
	 * @return Returns the credentialsNonExpired.
	 */
	@Transient
	public boolean isCredentialsNonExpired() {
		return true;
	}

	/**
	 * @see org.acegisecurity.userdetails.UserDetails#isEnabled()
	 * @return Returns the enabled.
	 */
	@Override
	public boolean isEnabled() {
		return this.enabled;
	}

	public void setEnabled(boolean enabled) {
		this.enabled = enabled;
	}

	public String getVerificationKey() {
		return verificationKey;
	}

	public void setVerificationKey(String verificationKey) {
		this.verificationKey = verificationKey;
	}

	/**
	 * @return the lastLoginDate
	 */
	public Date getLastLoginDate() {
		return lastLoginDate;
	}

	/**
	 * @param lastLoginDate the lastLoginDate to set
	 */
	public void setLastLoginDate(Date lastLoginDate) {
		this.lastLoginDate = lastLoginDate;
	}

	/* (non-Javadoc)
	 * @see org.acegisecurity.userdetails.UserDetails#getAuthorities()
	 */
	@Transient
	@Override
	public Collection<GrantedAuthority> getAuthorities() {
		@Bound("userToRoles") int i;
		@Inv("= (- roles it) (- c355 c354) ") final Set <GrantedAuthority> roles = new HashSet<GrantedAuthority>();

		@Iter("<= it userToRoles") Iterator<UserToRole> it = userToRoles.iterator();
		while (it.hasNext()) {
			UserToRole userToRole;
			c354: userToRole = it.next();
			c355: roles.add(userToRole.getRole());
		}

		return roles;

	}

	@Override
	public String toString()
	{
		final String TAB = " | ";

		@Bound("19") int i;
		@Inv("= retValue (+ c369 c370 c371 c372 c373 c374 c375 c376 c377 c378 c379 c380 c381 c382 c383 c384 c385 c386 c387)") final StringBuilder retValue = new StringBuilder();

		c369: retValue.append("User ( ");
		c370: retValue.append(super.toString());
		c371: retValue.append(TAB);
		c372: retValue.append("id = ");
		c373: retValue.append(this.getId());
		c374: retValue.append(TAB);
		c375: retValue.append("Username = ");
		c376: retValue.append(this.getUsername());
		c377: retValue.append(TAB);
		c378: retValue.append("Email = ");
		c379: retValue.append(this.getEmail());
		c380: retValue.append(TAB);
		c381: retValue.append("FirstName = ");
		c382: retValue.append(this.getFirstName());
		c383: retValue.append(TAB);
		c384: retValue.append("LastName = ");
		c385: retValue.append(this.getLastName());
		c386: retValue.append(TAB);
		c387: retValue.append(" )");

		return retValue.toString();
	}

}
