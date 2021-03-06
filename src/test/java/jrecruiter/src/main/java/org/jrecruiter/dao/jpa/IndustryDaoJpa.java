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
package org.jrecruiter.dao.jpa;

import java.util.List;

import javax.persistence.Query;

import org.jrecruiter.dao.IndustryDao;
import org.jrecruiter.model.Industry;
import org.springframework.stereotype.Repository;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

/**
 *
 * @author Gunnar Hillert
 */
@Repository("industryDao")
public final class IndustryDaoJpa extends GenericDaoJpa< Industry, Long>
								  implements IndustryDao {

	/**
	 * Constructor.
	 *
	 */
	private IndustryDaoJpa() {
		super(Industry.class);
	}

	@SuppressWarnings("unchecked")
	public List<Industry> getAllIndustriesOrdered() {

		@InvUnk("Unknown API") final List<Industry> industries;

		final Query query = entityManager.createQuery(
				"select ind from Industry ind " +
				"order by name ASC");

		industries = query.getResultList();

		return industries;
	}


}
