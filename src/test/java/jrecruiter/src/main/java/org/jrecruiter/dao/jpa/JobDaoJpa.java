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

import java.util.Calendar;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.persistence.FlushModeType;
import javax.persistence.NoResultException;
import javax.validation.constraints.NotNull;
import javax.validation.constraints.Past;

import org.apache.lucene.queryParser.MultiFieldQueryParser;
import org.apache.lucene.util.Version;
import org.hibernate.Criteria;
import org.hibernate.Query;
import org.hibernate.Session;
import org.hibernate.criterion.Order;
import org.hibernate.criterion.Restrictions;
import org.hibernate.search.jpa.FullTextEntityManager;
import org.hibernate.search.jpa.Search;
import org.jrecruiter.common.CollectionUtils;
import org.jrecruiter.dao.JobDao;
import org.jrecruiter.model.Industry;
import org.jrecruiter.model.Job;
import org.jrecruiter.model.Region;
import org.springframework.stereotype.Repository;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

/**
 * This DAO provides job-related database methods.
 *
 * @author Puchala, Gunnar Hillert
 */
@Repository("jobDao")
public final class JobDaoJpa extends GenericDaoJpa< Job, Long>
implements JobDao {

	/**
	 * Constructor.
	 *
	 */
	private JobDaoJpa() {
		super(Job.class);
	}



	/**
	 * Method for returning list of all jobs.
	 *
	 * @return List of Jobs
	 *
	 */
	@SuppressWarnings("unchecked")
	public List < Job > getAllJobs() {

		@InvUnk("Unknown API") List < Job > jobs = entityManager
		.createQuery("select job from Job job "
				+ "left outer join fetch job.statistic "
				+ " order by job.updateDate DESC")
				.getResultList();

		return jobs;
	}

	/**
	 * Method for getting users jobs.
	 *
	 * @param username name of user owning the job.
	 * @return List of Job objects for given User
	 * @see org.jrecruiter.persistent.dao.
	 *      JobReqDAO#getAllUserJobs(java.lang.String)
	 */
	@SuppressWarnings("unchecked")
	public List < Job > getAllUserJobs(final String username) {

		@InvUnk("Unknown API") List < Job > jobs = entityManager
		.createQuery("from Job j where j.user.username=:username")
		.setParameter("username", username)
		.getResultList();
		return jobs;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see org.jrecruiter.persistent.dao.
	 *      JobReqDAO#getAllUserJobs(java.lang.String)
	 */
	@SuppressWarnings("unchecked")
	public List < Job > getAllUserJobsForStatistics(Long userId) {

		@InvUnk("Unknown API") List < Job > jobs = entityManager
		.createQuery("from Job j left outer join fetch j.statistic where j.user.id=:userId")
		.setParameter("userId", userId)
		.getResultList();
		return jobs;
	}

	/**
	 * Method for returning list of jobs owned by the user for statistical
	 * purposes.
	 *
	 * @param username username for which statistics shall be obtained
	 * @param maxResult maximum number of statistics objects returned
	 * @param statsMode  what type of statistical information to be generated
	 * @return List of jobs.
	 *
	 * @see org.jrecruiter.dao.JobsDao#getUsersJobsForStatistics(java.lang.String,
	 *      java.lang.Integer, org.jrecruiter.common.Constants.StatsMode)
	 */
	@SuppressWarnings("unchecked")
	public List < Job > getUsersJobsForStatistics(final Long userId,
			final Integer maxResult,
			final Boolean administrator) {

		@InvUnk("Unknown API") final List < Job > jobs;

			javax.persistence.Query query = null;

			if (administrator) {

				query = entityManager
				.createQuery("select j from Job j left outer join fetch j.statistic as stats "
						+ "where stats is not null order by stats.counter desc");

			} else {

				query = entityManager
				.createQuery("select j from Job j left outer join fetch j.statistic as stats "
						+ "where j.user.id=:userId and stats is not null "
						+ "order by stats.counter desc");
				query.setParameter("userId", userId);
			}

			query.setMaxResults(maxResult);

			jobs = query.getResultList();

			return jobs;
		}

		/**
		 * Perform a simple search within the persistence store.
		 *
		 * @param keyword
		 *            The search keyword
		 * @return List of job postings representing the search results.
		 */
		@SuppressWarnings("unchecked")
		public List<Job> searchByKeyword(final String keyword) {

			FullTextEntityManager fullTextEntityManager = Search.getFullTextEntityManager(entityManager);

			MultiFieldQueryParser parser = new MultiFieldQueryParser(Version.LUCENE_CURRENT,
					new String[]{"description", "industry.name", "region.name", "regionOther",
						"jobTitle", "website", "businessAddress1", "businessAddress2",
						"businessCity", "businessState", "businessZip", "businessPhone",
						"businessEmail", "industryOther", "jobRestrictions",
						"updateDate"},
						fullTextEntityManager.getSearchFactory().getAnalyzer( Job.class ));
			try {
			org.apache.lucene.search.Query query = parser.parse(keyword);

			javax.persistence.Query hibQuery = fullTextEntityManager.createFullTextQuery( query, Job.class );
			@InvUnk("Unknown API") List<Job> result = hibQuery.getResultList();

			return result;

			  } catch ( org.apache.lucene.queryParser.ParseException e) {
				throw new IllegalStateException(e);
			}

		}

		/**
		 * Method for returning list of available job postings.
		 * @param pageSize Max number of results returned
		 * @param pageNumber Which page are you one?
		 * @param fieldSorted Which field shall be sorted
		 * @param sortOrder What is the sort order?
		 * @return List of jobs.
		 */
		@SuppressWarnings("unchecked")
		public List < Job > getJobs(final Integer pageSize,
									final Integer pageNumber,
									Map<String, String> sortOrders,
									Map<String, String> jobFilters) {
			@InvUnk("Unknown API") List < Job > jobs;

			if (pageSize == null) {
				throw new IllegalStateException("pageSize must not be null.");
			}
			if (pageNumber == null) {
				throw new IllegalStateException("pageNumber must not be null.");
			}

			if (sortOrders == null) {
				sortOrders = CollectionUtils.getHashMap();
			}

			if (sortOrders.isEmpty()) {
				sortOrders.put("updateDate", "ASC");
			}

			if (jobFilters == null) {
				jobFilters = CollectionUtils.getHashMap();
			}


			Session session = (Session)entityManager.getDelegate();
			final Criteria criteria = session.createCriteria(Job.class);

			//criteria.setFetchMode("statistics", FetchMode.JOIN);
			//criteria.setFetchMode("region", FetchMode.JOIN);

			for (Entry<String, String> entry : sortOrders.entrySet()) {
				if (entry.getValue().equalsIgnoreCase("DESC")) {
					criteria.addOrder(Order.desc(entry.getKey()));
				} else if (entry.getValue().equalsIgnoreCase("ASC")) {
					criteria.addOrder(Order.asc(entry.getKey()));
				} else {
					throw new IllegalStateException("SortOrder " + entry.getValue() + " is not supported.");
				}
			}

			for (Entry<String, String> entry : jobFilters.entrySet()) {
					criteria.add(Restrictions.ilike(entry.getKey(), entry.getValue()));
			}

			criteria.setFirstResult((pageNumber - 1) * pageSize);
			criteria.setMaxResults(pageSize);

			jobs = criteria.list();

			return jobs;
		}


		/**
		 * Returns the number of totally available jobs in the system.
		 *
		 * @return Total number of jobs
		 * @see org.jrecruiter.dao.JobsDao#getJobsCount()
		 */
		public Long getJobsCount() {

			Long numberOfJobs = null;

			Session session = (Session)entityManager.getDelegate();
			Query query = session.createQuery("select count(*) from Job");
			numberOfJobs = (Long) query.uniqueResult();

			return numberOfJobs;
		}

		/** {@inheritDoc} */
		@SuppressWarnings("unchecked")
		public void reindexSearch() {

			final FullTextEntityManager fullTextEntityManager = Search.getFullTextEntityManager(entityManager);
			fullTextEntityManager.setFlushMode(FlushModeType.COMMIT);

			@InvUnk("Unknown API") final List<Job> jobs = entityManager.createQuery("select job from Job as job").getResultList();

			for (final Job job : jobs) {
				fullTextEntityManager.index(job);
			}

			@InvUnk("Unknown API") final List<Region> regions = entityManager.createQuery("select region from Region as region").getResultList();

			for (final Region region : regions) {
				fullTextEntityManager.index(region);
			}

			@InvUnk("Unknown API") final List<Industry> industries = entityManager.createQuery("select industry from Industry as industry").getResultList();

			for (final Industry industry : industries) {
				fullTextEntityManager.index(industry);
			}

		}

		/** {@inheritDoc} */
		@SuppressWarnings("unchecked")
		public List<Job> getJobSummaries() {

			@InvUnk("Unknown API") final List < Job > jobs = entityManager
			.createQuery("select new Job(j.id, j.businessName, j.jobTitle, j.region, j.updateDate, j.usesMap, j.latitude, j.longitude, j.zoomLevel) from Job j left outer join j.region order by j.updateDate desc")
			.getResultList();
			return jobs;
		}

		/* (non-Javadoc)
		 * @see org.jrecruiter.dao.JobDao#getForUniversalId(java.lang.Long)
		 */
		@Override
		public Job getForUniversalId(final String universalId) {

			Job job;

			try {
				job = (Job) entityManager
				.createQuery("select j from Job j where j.universalId = :universalId")
				.setParameter("universalId", universalId)
				.getSingleResult();
			} catch(NoResultException e) {
				job = null;
			}

			return job;
		}



		@SuppressWarnings("unchecked")
		@Override
		public List<Job> getJobsByUpdateDate(@NotNull @Past final Calendar updateDate) {

			@InvUnk("Unknown API") final List<Job> jobs;

			jobs = entityManager
				.createQuery("select j from Job j where j.updateDate <= :updateDate")
				.setParameter("updateDate", updateDate.getTime())
				.getResultList();

			return jobs;
		}


	}


