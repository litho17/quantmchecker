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
package org.jrecruiter.dao.hibernate;

import java.io.FileWriter;
import java.io.IOException;
import java.sql.SQLException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.persistence.Persistence;
import javax.persistence.spi.PersistenceProvider;
import javax.persistence.spi.PersistenceProviderResolver;
import javax.persistence.spi.PersistenceProviderResolverHolder;
import javax.persistence.spi.PersistenceUnitInfo;
import javax.sql.DataSource;

import org.hibernate.HibernateException;
import org.hibernate.cfg.Configuration;
import org.hibernate.tool.hbm2ddl.SchemaExport;
import org.jrecruiter.dao.SystemDao;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.orm.jpa.LocalContainerEntityManagerFactoryBean;
import org.springframework.stereotype.Repository;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

@Repository("systemDao")
public class SystemDaoHibernate implements SystemDao {

	private @Autowired DataSource dataSource;
	private @Autowired LocalContainerEntityManagerFactoryBean fb;

	/* (non-Javadoc)
	 * @see org.jrecruiter.service.DemoService#createDatabase()
	 */
	@Override
	public void updateDatabase() {

		@Bound("3") int i;
		PersistenceUnitInfo persistenceUnitInfo = fb.getPersistenceUnitInfo();
		@Inv("= props (+ c60 c61 c62)") Map<String, Object> props = fb.getJpaPropertyMap();

		try (FileWriter out = new FileWriter("schema-komplett.sql")) {
		//Map<String, Object> props = new HashMap<>();
		c60: props.put("javax.persistence.schema-generation.scripts.action", "update");
		c61: props.put("javax.persistence.schema-generation.scripts.create-target", out);
		c62: props.put("hibernate.connection.provider_class", "org.jrecruiter.service.impl.DemoServiceImpl.HibernateHack");
		Persistence.generateSchema(persistenceUnitInfo.getPersistenceUnitName(), props);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

	/* (non-Javadoc)
	 * @see org.jrecruiter.service.DemoService#createDatabase()
	 */
	@Override
	public void createDatabase() {

		@Bound("7") int i;
		CustomPersistenceProviderResolver.persistenceProvider = fb.getPersistenceProvider();
		PersistenceProviderResolverHolder.setPersistenceProviderResolver(new CustomPersistenceProviderResolver());
		HibernateHack.dataSource = this.dataSource;

		PersistenceUnitInfo persistenceUnitInfo = fb.getPersistenceUnitInfo();
		//Map<String, Object> props = fb.getJpaPropertyMap();
		@Inv("= props (+ c84 c85 c86 c87 c96 c97 c98)") Map<String, Object> props = new HashMap<String, Object>();
		c84: props.put("hibernate.id.new_generator_mappings", true);
		c85: props.put("hibernate.query.substitutions", "true '1', false '0'");
		c86: props.put("hibernate.dialect", "org.hibernate.dialect.H2Dialect");
		c87: props.put("hibernate.ejb.naming_strategy", "org.jrecruiter.hibernate.ImprovedPluralizedNamingStrategy");
		//fb.getPersistenceProvider()
		for (Entry<String, Object> entry : props.entrySet()) {
			System.out.println(">>>>" + entry.getKey());
			System.out.println(">>>>" + entry.getValue());
		}

		try (FileWriter out = new FileWriter("/tmp/schema-komplett-create.sql")) {
		//Map<String, Object> props = new HashMap<>();
		c96: props.put("javax.persistence.schema-generation.database.action", "create");
		c97: props.put("javax.persistence.schema-generation.connection", this.dataSource);
		c98: props.put("javax.persistence.schema-generation.scripts.create-target", out);
		//props.put("hibernate.connection.provider_class", "org.jrecruiter.service.impl.DemoServiceImpl.HibernateHack");

		fb.getPersistenceProvider().generateSchema(persistenceUnitInfo, props);

		//Persistence.generateSchema(persistenceUnitInfo.getPersistenceUnitName(), props);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

	private static class HibernateHack {
		public static DataSource dataSource;
	}

	static class CustomPersistenceProviderResolver implements PersistenceProviderResolver {

		public static PersistenceProvider persistenceProvider;

		@Override
		public List<PersistenceProvider> getPersistenceProviders() {
			return Arrays.<PersistenceProvider> asList(persistenceProvider);
		}

		@Override
		public void clearCachedProviders() {}
	}

}
