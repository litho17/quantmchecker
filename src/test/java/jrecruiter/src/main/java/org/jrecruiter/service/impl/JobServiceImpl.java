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

import static com.rosaloves.bitlyj.Bitly.as;
import static com.rosaloves.bitlyj.Bitly.shorten;

import java.net.URI;
import java.net.URISyntaxException;
import java.util.Calendar;
import java.util.Date;
import java.util.List;
import java.util.Map;

import javax.validation.constraints.NotNull;

import org.jrecruiter.common.AcegiUtil;
import org.jrecruiter.common.ApiKeysHolder;
import org.jrecruiter.common.CalendarUtils;
import org.jrecruiter.common.CollectionUtils;
import org.jrecruiter.common.Constants.Roles;
import org.jrecruiter.common.Constants.ServerActions;
import org.jrecruiter.dao.ConfigurationDao;
import org.jrecruiter.dao.IndustryDao;
import org.jrecruiter.dao.JobCountPerDayDao;
import org.jrecruiter.dao.JobDao;
import org.jrecruiter.dao.RegionDao;
import org.jrecruiter.dao.StatisticDao;
import org.jrecruiter.dao.UserDao;
import org.jrecruiter.model.Configuration;
import org.jrecruiter.model.Industry;
import org.jrecruiter.model.Job;
import org.jrecruiter.model.ServerSettings;
import org.jrecruiter.model.Statistic;
import org.jrecruiter.model.User;
import org.jrecruiter.model.statistics.JobCountPerDay;
import org.jrecruiter.service.JobService;
import org.jrecruiter.service.NotificationService;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Propagation;
import org.springframework.transaction.annotation.Transactional;
import org.jrecruiter.model.Region;

import com.rosaloves.bitlyj.Url;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;

/**
 * @author Gunnar Hillert
 */
@Transactional
@Service("jobService")
public class JobServiceImpl implements JobService {

	/** Initialize Logging. */
	private final static Logger LOGGER = LoggerFactory.getLogger(JobServiceImpl.class);

	/** Job Dao. */
	private @Autowired JobDao jobDao;

	/** Job Count Per Day Dao. */
	private @Autowired JobCountPerDayDao jobCountPerDayDao;

	/** User Dao. */
	private @Autowired UserDao userDao;

	/** Industry Dao. */
	private @Autowired IndustryDao industryDao;

	/** User Region Dao. */
	private @Autowired RegionDao regionDao;

	/** Statistic Dao. */
	private @Autowired StatisticDao statisticDao;

	/** Settings Dao. */
	private @Autowired ConfigurationDao configurationDao;

	private @Autowired NotificationService  notificationService;

	private @Autowired ServerSettings serverSettings;

	private @Autowired ApiKeysHolder apiKeysHolder;

	//~~~~~Business Methods~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public List<Job> getJobs() {
		return jobDao.getAllJobs();
	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public List<Job> getJobs(Integer pageSize, Integer pageNumber, Map<String, String> sortOrders, Map<String, String> jobFilters) {
		return jobDao.getJobs(pageSize, pageNumber, sortOrders, jobFilters);
	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public Long getJobsCount() {
		return jobDao.getJobsCount();
	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public List<Job> getUsersJobs(final String username) {

		User user = userDao.getUser(username);

		boolean administrator = false;

		if (AcegiUtil.containsRole(user.getAuthorities(), Roles.ADMIN.name())) {
			administrator = true;
		}
		return administrator? jobDao.getAllJobs() : jobDao.getAllUserJobs(username);
	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public List<Job> getUsersJobsForStatistics(final String username) {

		final User user = userDao.getUser(username);

		if (user == null) {
			throw new IllegalArgumentException("No user found for username " + username);
		}

		if (AcegiUtil.hasRole(Roles.ADMIN.name())) {
			return jobDao.getAll();
		}

		return jobDao.getAllUserJobsForStatistics(user.getId());
	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public List<Job> getUsersJobsForStatistics(String username, Integer maxResult) {

		final User user = userDao.getUser(username);

		if (user == null) {
			throw new IllegalArgumentException("No user found for username " + username);
		}

		boolean administrator = false;

		if (AcegiUtil.hasRole(Roles.ADMIN.name())) {
			administrator = true;
		}

		return jobDao.getUsersJobsForStatistics(user.getId(), maxResult, administrator);
	}

	/** {@inheritDoc} */
	@Override
	public Job addJob(final Job job) {

		if (job.getStatistic() == null) {
			Statistic statistic = new Statistic(job.getId(), Long.valueOf(0), null, Long.valueOf(0));
			statistic.setJob(job);
			job.setStatistic(statistic);
		}

		final Job savedJob = jobDao.save(job);

		saveJobStatistics(job);

		return savedJob;
	}

	/** {@inheritDoc} */
	@Override
	public void addJobAndSendToMailingList(final Job job) {
		final Job savedJob = this.addJob(job);
		@Bound("18") int i;

		@Inv("= context (+ c208 c209 c210 c211 c212 c213 c214 c215 c216)") final Map<String, Object> context = CollectionUtils.getHashMap();
		c208: context.put("jobId", savedJob.getId());
		c209: context.put("jobTitle", savedJob.getJobTitle());
		c210: context.put("businessLocation", savedJob.getRegionOther());
		c211: context.put("businessName", savedJob.getBusinessName());
		c212: context.put("description", savedJob.getDescription());
		c213: context.put("jobRestrictions", savedJob.getJobRestrictions());
		c214: context.put("updateDate", savedJob.getUpdateDate());
		c215: context.put("businessEmail", savedJob.getBusinessEmail());
		c216: context.put("serverAddress", serverSettings.getServerAddress());

		@Iter("= emailRequest.context context") final EmailRequest emailRequest = new EmailRequest(
				((Configuration) this.getJRecruiterSetting("mail.jobposting.email")).getMessageText(), savedJob.getJobTitle(), context, "add-job");
		notificationService.sendEmail(emailRequest);
		final String tweetMessage = "New Job: " + savedJob.getJobTitle() + " @ " + savedJob.getBusinessName();

		final URI uri = createShortenedJobDetailUrl(savedJob);
		notificationService.sendTweetToTwitter(tweetMessage + ": " + uri.toString());

	}

	private URI createShortenedJobDetailUrl(final Job job) {
		final String jobUrlString = this.serverSettings.getServerAddress() + ServerActions.JOB_DETAIL.getPath() + "?jobId=" + job.getId();

		final URI jobUri;

		try {
			jobUri = new URI(jobUrlString);
		} catch (URISyntaxException e) {
			throw new IllegalStateException("Cannot create URI for " + jobUrlString);
		}

		if (this.apiKeysHolder.isBitlyEnabled()) {
			return this.shortenUrl(jobUri.toString());
		}
		else {
			return jobUri;
		}

	}

	/** {@inheritDoc} */
	public URI shortenUrl(final String urlAsString) {

		//FIXME Handle this better
		Url url = as(apiKeysHolder.getBitlyUsername(),
					apiKeysHolder.getBitlyPassword())
				.call(shorten(urlAsString));
		try {
			return new URI(url.getShortUrl());
		} catch (URISyntaxException e) {
			throw new IllegalArgumentException(
					String.format("Please provide a valid URI - %s is not valid", urlAsString));
		}

	}

	/** {@inheritDoc} */
	@Override
	public void updateJob(final Job job) {

		if (job.getStatistic() == null) {
			Statistic statistic = new Statistic(job.getId(), Long.valueOf(0), null, Long.valueOf(0));
			statistic.setJob(job);
			job.setStatistic(statistic);
		}

		final Job savedJob = jobDao.save(job);

		saveJobStatistics(savedJob);

		String tweetMessage = "Job Update: " + job.getJobTitle() + " @ " + job.getBusinessName();

		final URI uri = createShortenedJobDetailUrl(job);

		tweetMessage = tweetMessage + ": " + uri.toString();
	  //  notificationService.sendTweetToTwitter(tweetMessage);

	}

	/** {@inheritDoc} */
	public void saveJobStatistics(Job job) {

		if (job.getId() == null) {

			JobCountPerDay jobCountPerDay = jobCountPerDayDao.getByDate(job.getRegistrationDate());

			if (jobCountPerDay == null) {
				jobCountPerDay = new JobCountPerDay();
				jobCountPerDay.setJobDate(job.getRegistrationDate());
				jobCountPerDay.setNumberOfJobsDeleted(Long.valueOf(0));
				jobCountPerDay.setNumberOfJobsPosted(Long.valueOf(1));
				jobCountPerDay.setTotalNumberOfJobs(jobDao.getJobsCount());
				jobCountPerDayDao.save(jobCountPerDay);
			} else {
				jobCountPerDay.setNumberOfJobsPosted(jobCountPerDay.getNumberOfJobsPosted() + 1);
				jobCountPerDay.setTotalNumberOfJobs(jobDao.getJobsCount() + 1);
				jobCountPerDayDao.save(jobCountPerDay);
			}
		}
	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public Job getJobForId(final Long jobId) {
		return jobDao.get(jobId);
	}

	/* (non-Javadoc)
	 * @see org.jrecruiter.service.JobService#getJobForUniversalId(java.lang.Long)
	 */
	@Override
	public Job getJobForUniversalId(final String universalId) {
		return jobDao.getForUniversalId(universalId);
	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public List<Job> searchByKeyword(final String keyword) {
		return jobDao.searchByKeyword(keyword);
	}

	/** {@inheritDoc} */
	@Override
	public void deleteJobForId(final Long jobId) {
		jobDao.remove(jobId);

		JobCountPerDay jobCountPerDay = jobCountPerDayDao.getByDate(new Date());

		if (jobCountPerDay == null) {
			jobCountPerDay = new JobCountPerDay();
			jobCountPerDay.setJobDate(new Date());
		}

		jobCountPerDay.setNumberOfJobsDeleted(Long.valueOf(1));
		jobCountPerDay.setNumberOfJobsPosted(Long.valueOf(0));
		jobCountPerDay.setTotalNumberOfJobs(jobDao.getJobsCount());
		jobCountPerDayDao.save(jobCountPerDay);
	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public List<Configuration> getJRecruiterSettings() {
		return configurationDao.getAll();
	}

	/** {@inheritDoc} */
	@Override
	public Configuration getJRecruiterSetting(final String key) {
		return configurationDao.get(key);
	}

	/** {@inheritDoc} */
	@Override
	public void saveJRecruiterSetting(final Configuration configuration) {
		configurationDao.save(configuration);

	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public List<Industry> getIndustries() {
		return this.industryDao.getAllIndustriesOrdered();
	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public List<Region> getRegions() {
		return this.regionDao.getAllRegionsOrdered();
	}

	/** {@inheritDoc} */
	@Override
	public void updateJobStatistic(Statistic statistics) {
			this.statisticDao.save(statistics);
	}

	/** {@inheritDoc} */
	@Override
	public void reindexSearch() {
		jobDao.reindexSearch();
	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public Industry getIndustry(Long industryId) {
		return industryDao.get(industryId);
	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public Region getRegion(Long regionId) {
		return regionDao.get(regionId);
	}

	/** {@inheritDoc} */
	@Override
	@Transactional(readOnly = true, propagation=Propagation.SUPPORTS)
	public List<JobCountPerDay> getJobCountPerDayAndPeriod(final Date fromDate, final Date toDate) {

		//Make sure we have values at least for today and the previous day.
		this.updateJobCountPerDays();

		@InvUnk("Dynamic dispatch") final List<JobCountPerDay> jobCountPerDays = jobCountPerDayDao.getJobCountPerDayAndPeriod(fromDate, toDate);
		return jobCountPerDays;
	}

	/** {@inheritDoc} */
	@Override
	public void updateJobCountPerDays() {
		this.updateJobCountPerDays(CalendarUtils.getCalendarWithoutTime());
	}

	/** {@inheritDoc} */
	@Override
	public void updateJobCountPerDays(final Calendar asOfDay) {

		final Calendar today = CalendarUtils.getCalendarWithoutTime();
		today.setTime(asOfDay.getTime());
		final Calendar yesterday = CalendarUtils.getCalendarWithoutTime();
		yesterday.add(Calendar.DAY_OF_YEAR, -1);

		@InvUnk("Dynamic dispatch") final List<JobCountPerDay> latestTwoJobCountPerDays = jobCountPerDayDao.getLatestTwoJobCounts();

		//If nothing exists yet, create an entry with zero jobs.
		if (latestTwoJobCountPerDays.isEmpty()) {
			jobCountPerDayDao.save(new JobCountPerDay(yesterday.getTime(), 0L, 0L, 0L));
		}

		boolean containsToday = false;

		//Let's make sure we have a value for today
		for (JobCountPerDay jobCountPerDay : latestTwoJobCountPerDays) {
			if (today.getTime().equals(jobCountPerDay.getJobDate())) {
				containsToday = true;
				break;
			}
		}

		if (!containsToday) {
			//We need to create a value for today
			final Long totalNumberOfJobs = this.getJobsCount();
			jobCountPerDayDao.save(new JobCountPerDay(today.getTime(), 0L, 0L, totalNumberOfJobs));
		}

	}

	/** {@inheritDoc} */
	@Override
	public void removeOldJobs(final @NotNull Integer days) {

		final Calendar cal = CalendarUtils.getCalendarWithoutTime();
		cal.add(Calendar.DAY_OF_YEAR, days.intValue() * -1);

		@InvUnk("Dynamic dispatch") final List<Job> jobs = jobDao.getJobsByUpdateDate(cal);

		LOGGER.info("Found " + jobs.size() + " jobs that are eligible for removal.");

		if (!jobs.isEmpty()) {

			final long jobsCount = jobDao.getJobsCount();

			for (final Job job : jobs) {
				jobDao.remove(job.getId());
			}

			JobCountPerDay jobCountPerDay = jobCountPerDayDao.getByDate(new Date());

			if (jobCountPerDay == null) {
				jobCountPerDay = new JobCountPerDay();
				jobCountPerDay.setJobDate(new Date());

			}

			jobCountPerDay.setNumberOfJobsDeleted(Long.valueOf(jobs.size()));
			jobCountPerDay.setNumberOfJobsPosted(Long.valueOf(0));
			jobCountPerDay.setTotalNumberOfJobs(jobsCount - jobs.size() );
			jobCountPerDay.setAutomaticallyCleaned(Boolean.TRUE);
			jobCountPerDayDao.save(jobCountPerDay);

		}

	}

}
