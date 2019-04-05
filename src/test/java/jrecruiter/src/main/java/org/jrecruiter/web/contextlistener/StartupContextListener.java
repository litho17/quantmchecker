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
package org.jrecruiter.web.contextlistener;

import java.io.File;

import javax.servlet.ServletContext;
import javax.servlet.ServletContextEvent;
import javax.servlet.ServletContextListener;

import org.apache.commons.lang.StringUtils;
import org.jrecruiter.common.Apphome;
import org.jrecruiter.common.SpringContextMode;
import org.jrecruiter.common.SystemInformationUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

/**
 * Prepare the logging infrastructure and select what constitutes the JRecruiter
 * Home directory.
 *
 * The JRECRUITER_HOME directory is either defined by an environment variable or
 * a system property. The main issue is that the logging infrastructure (in this
 * case logback) does not know about environment variables.
 *
 * Lockback (similar also Log4j) can only define a dynamic logging path/location
 * using a system property.
 *
 * An additional benefit of this context listener is that it give you a dynamic
 * choice of where the your home directory.
 *
 * First, it looks whether a JRECRUITER_HOME system property exists, and uses it
 * in case it is present. Otherwise it will look whether an environment variable
 * JRECRUITER_HOME exist, and uses it if present.
 *
 * If neither system property nor environment variable exist, an {@link IllegalStateException}
 * is thrown telling you to setup one or the other.
 *
 * @author Gunnar Hillert
 * @since 2.0
 *
 */
public class StartupContextListener implements ServletContextListener {

	private final static Logger LOGGER = LoggerFactory.getLogger(StartupContextListener.class);

	/**
	 * Default constructor.
	 */
	public StartupContextListener() {
		super();
	}

	/* (non-Javadoc)
	 * @see javax.servlet.ServletContextListener#contextDestroyed(javax.servlet.ServletContextEvent)
	 */
	@Override
	public void contextDestroyed(final ServletContextEvent servletContextEvent) {

	}

	/* (non-Javadoc)
	 * @see javax.servlet.ServletContextListener#contextInitialized(javax.servlet.ServletContextEvent)
	 */
	@Override
	public void contextInitialized(final ServletContextEvent servletContextEvent) {
		final ServletContext servletContext = servletContextEvent.getServletContext();

		final String         contextPath      = servletContext.getContextPath();
		final String         server           = servletContext.getServerInfo();

		final Apphome apphome = SystemInformationUtils.retrieveBasicSystemInformation();

		final String jrecruiterHomeMessage;
		SpringContextMode springContextMode = null;

		switch (apphome.getAppHomeSource()) {

			case SYSTEM_PROPERTY:
				jrecruiterHomeMessage = "System Property '" + Apphome.APP_HOME_DIRECTORY
									+ "' found: " + apphome.getAppHomePath();
				break;

			case ENVIRONMENT_VARIABLE:
				System.setProperty(Apphome.APP_HOME_DIRECTORY, apphome.getAppHomePath());

				jrecruiterHomeMessage = "Environment Variable '" + Apphome.APP_HOME_DIRECTORY
									+ "' found: " + apphome.getAppHomePath()
									+ ". Using it to set system property.";
				break;

			case USER_DIRECTORY:

				jrecruiterHomeMessage = "'" + Apphome.APP_HOME_DIRECTORY
									+ "' not found. Please set '" + Apphome.APP_HOME_DIRECTORY
									+ "' as a system property or as an environment variable. DEMO Mode, using embedded database.";
				break;
			default: throw new IllegalStateException("Was expecting to resolve a home directory.");

		}

		if (SystemInformationUtils.existsConfigFile(apphome.getAppHomePath())) {
			springContextMode = SpringContextMode.ProductionContextConfiguration;
		} else {
			springContextMode = SpringContextMode.DemoContextConfiguration;
		}

		System.setProperty("jrecruiter-spring-profile", springContextMode.getCode());

		if (System.getProperty("ehcache.disk.store.dir") == null) {
			System.setProperty("ehcache.disk.store.dir", System.getProperty(Apphome.APP_HOME_DIRECTORY) + File.separator + "ehcache");
		}

		@Bound("29") int i;
		@Inv("= bootMessage (+ c130 c131 c132 c133 c134 c135 c136 c137 c138 c143 c144 c145 c146 c147 c148 c149 c150 c151 c152 c153 c154 c155 c156 c157 c158 c159 c160 c161 c162)") final StringBuilder bootMessage = new StringBuilder();

		c130: bootMessage.append("\n");
		c131: bootMessage.append(jrecruiterHomeMessage);
		c132: bootMessage.append("\n");
		c133: bootMessage.append("Using Spring Context: " + springContextMode);
		c134: bootMessage.append("\n");
		c135: bootMessage.append("Booting jRecruiter...                          ");
		c136: bootMessage.append("\n");
		c137: bootMessage.append("-----------------------------------------------");
		c138: bootMessage.append("\n");

		final String contextPathLabel = StringUtils.rightPad("Context Path", 40, '.');
		final String serverLabel = StringUtils.rightPad("Server", 40, '.');

		c143: bootMessage.append(contextPathLabel + ": " + contextPath);
		c144: bootMessage.append("\n");
		c145: bootMessage.append(serverLabel      + ": " + server);
		c146: bootMessage.append("\n");
		c147: bootMessage.append("-----------------------------------------------");
		c148: bootMessage.append("\n");
		c149: bootMessage.append("Systen Properties:");
		c150: bootMessage.append("\n");
		c151: bootMessage.append("-----------------------------------------------");
		c152: bootMessage.append("\n");
		c153: bootMessage.append(SystemInformationUtils.getAllSystemProperties());
		c154: bootMessage.append("-----------------------------------------------");
		c155: bootMessage.append("\n");
		c156: bootMessage.append("Environment Variables:");
		c157: bootMessage.append("\n");
		c158: bootMessage.append("-----------------------------------------------");
		c159: bootMessage.append("\n");
		c160: bootMessage.append(SystemInformationUtils.getAllEnvironmentVariables());
		c161: bootMessage.append("-----------------------------------------------");
		c162: bootMessage.append("\n");

		LOGGER.info(bootMessage.toString());
	}

}
