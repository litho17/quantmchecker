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

import java.io.InputStream;
import java.util.*;

import javax.servlet.ServletContext;

import net.jforum.core.exceptions.ForumException;
import net.jforum.entities.Config;
import net.jforum.repository.ConfigRepository;

import org.apache.commons.configuration.ConfigurationException;
import org.apache.commons.configuration.PropertiesConfiguration;
import org.apache.commons.configuration.reloading.FileChangedReloadingStrategy;
import org.apache.log4j.Logger;
import org.hibernate.Session;
import org.hibernate.SessionFactory;

import br.com.caelum.vraptor.ioc.ApplicationScoped;
import br.com.caelum.vraptor.ioc.Component;
import plv.colorado.edu.quantmchecker.qual.*;

/**
 * @author Rafael Steil
 * @author Jose Donizetti Brito Junior
 */
@Component
@ApplicationScoped
public class JForumConfig extends PropertiesConfiguration {
	private static final Logger logger = Logger.getLogger(JForumConfig.class);
	private final SessionFactory sessionFactory;

	public JForumConfig(ServletContext servletContext, SessionFactory sessionFactory) {
		this.sessionFactory = sessionFactory;
		this.setReloadingStrategy(new FileChangedReloadingStrategy());
		this.setDelimiterParsingDisabled(true);

		try {
			loadProps();
			if (servletContext != null) {
				setProperty(ConfigKeys.APPLICATION_PATH, servletContext.getRealPath(""));
			}
			loadDatabaseProperties();
			normalizeTemplateDirectory();
		}
		catch (Exception e) {
			throw new ForumException(e);
		}
	}

	private void normalizeTemplateDirectory() {
		@Bound("2") int i;
		@Inv("= sb (+ c66 c70)") StringBuilder sb = new StringBuilder(getValue(ConfigKeys.TEMPLATE_DIRECTORY));

		if (sb.charAt(0) != '/') {
			c66: sb.insert(0, '/');
		}

		if (sb.charAt(sb.length() - 1) != '/') {
			c70: sb.append('/');
		}

		setProperty(ConfigKeys.TEMPLATE_DIRECTORY, sb.toString());
	}

	@Override
	public void setProperty(String key, Object value) {
		clearProperty(key);
		super.setProperty(key, value);
	}

	public List<String> getValueAsList(String key) {
		@Bound("key") int j;
		String value = getValue(key);
		@Inv("= (- l i) (- c90 c91)") List<String> l = new ArrayList<String>();

		if (value != null) {
			String[] parts = value.split(",");
			@Iter("<= i key") int i = 0;
			for (; i < parts.length;) {
				String p = parts[i];
				c90: l.add(p.trim());
				c91: i++;
			}
		}

		return l;
	}

	private void loadProps() throws ConfigurationException, Exception {
		this.load(this.getClass().getResourceAsStream("/jforumConfig/SystemGlobals.properties"));
		this.loadCustomProperties();
	}

	private void loadCustomProperties() throws Exception {
		InputStream is = this.getClass().getResourceAsStream("/jforumConfig/jforum-custom.properties");

		if (is != null) {
			Properties custom = new Properties();
			custom.load(is);

			for (Enumeration<?> e = custom.keys(); e.hasMoreElements(); ) {
				String key = (String)e.nextElement();
				this.clearProperty(key);
				this.addProperty(key, custom.get(key));
			}
		}
	}

	private void loadDatabaseProperties() {
		Session session = null;

		try {
			session = sessionFactory.openSession();

			ConfigRepository repository = new ConfigRepository(session);
			@InvUnk("Unknown API") List<Config> databasesProperties = repository.getAll();

			for (Config config : databasesProperties) {
				this.clearProperty(config.getName());
				this.addProperty(config.getName(), config.getValue());
			}
		}
		catch (Exception e) {
			logger.error("Error while trying to load custom settings from the database: " + e.getMessage(), e);
		}
		finally {
			try { session.close(); }
			catch (Exception e) {}
		}
	}

	/**
	 * @see org.apache.commons.configuration.BaseConfiguration#addPropertyDirect(java.lang.String, java.lang.Object)
	 */
	@Override
	protected void addPropertyDirect(String key, Object value) {
		super.addPropertyDirect(key, value);
	}

	/**
	 * Gets the complete path to the application root directory
	 * @return the path to the root directory
	 */
	public String getApplicationPath() {
		return this.getString(ConfigKeys.APPLICATION_PATH);
	}

	/**
	 * Delegates to {@link #getString(String)}
	 * @param key the key to retrieve
	 * @return the key's value
	 */
	public String getValue(String key) {
		return this.getString(key);
	}
}
