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
package net.jforum.controllers;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.Properties;

import javax.servlet.http.HttpServletRequest;

import net.jforum.actions.helpers.Domain;
import net.jforum.core.SecurityConstraint;
import net.jforum.security.AdministrationRule;
import net.jforum.services.ConfigService;
import net.jforum.util.JForumConfig;
import br.com.caelum.vraptor.Path;
import br.com.caelum.vraptor.Resource;
import br.com.caelum.vraptor.Result;
import plv.colorado.edu.quantmchecker.qual.*;

/**
 * @author Jose Donizetti de Brito Junior
 * @author Rafael Steil
 */
@Resource
@Path(Domain.CONFIG_ADMIN)
@SecurityConstraint(value = AdministrationRule.class, displayLogin = true)
public class ConfigController {
	private final ConfigService service;
	private final HttpServletRequest request;
	private final JForumConfig config;
	private final Result result;

	public ConfigController(ConfigService service, HttpServletRequest request, JForumConfig config, Result result) {
		this.service = service;
		this.request = request;
		this.config = config;
		this.result = result;
	}

	public void list() throws Exception {
		this.result.include("locales", this.loadLocaleNames());
		this.result.include("config", this.config);
	}

	@Summary({"this.service.i18n.messages", "1"})
	public void save() throws Exception {
		this.service.save(this.request);
		this.result.redirectTo(this).list();
	}

	private List<String> loadLocaleNames() throws Exception {
		@Bound("locales") int i;
		Properties locales = new Properties();

		locales.load(this.getClass().getResourceAsStream("/jforumConfig/languages/locales.properties"));

		@Inv("= (- localesList e) (- c74 c73)") List<String> localesList = new ArrayList<String>();

		@Iter("<= e locales") Enumeration<?> e = locales.keys();
		Object s;
		while (e.hasMoreElements()) {
			c73: s = e.nextElement();
			c74: localesList.add((String)s);
		}

		return localesList;
	}
}
