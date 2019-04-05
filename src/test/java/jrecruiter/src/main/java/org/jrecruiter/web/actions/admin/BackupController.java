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
package org.jrecruiter.web.actions.admin;

import java.io.IOException;
import java.io.OutputStream;
import java.util.List;

import javax.xml.bind.JAXBException;
import javax.xml.transform.stream.StreamResult;

import org.jrecruiter.dao.IndustryDao;
import org.jrecruiter.dao.JobCountPerDayDao;
import org.jrecruiter.dao.RegionDao;
import org.jrecruiter.dao.RoleDao;
import org.jrecruiter.model.*;
import org.jrecruiter.model.export.Backup;
import org.jrecruiter.model.statistics.JobCountPerDay;
import org.jrecruiter.service.JobService;
import org.jrecruiter.service.SystemSetupService;
import org.jrecruiter.service.UserService;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.oxm.jaxb.Jaxb2Marshaller;
import org.springframework.stereotype.Controller;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.ui.ModelMap;
import org.springframework.validation.BindingResult;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.multipart.MultipartFile;
import org.springframework.web.multipart.commons.CommonsMultipartResolver;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

/**
 * Retrieves all jobs and returns an XML document. The structure conforms to the layout
 * defined by Indeed.com
 *
 * @author Gunnar Hillert
 */
@Controller
public class BackupController {

	private static final Logger LOGGER = LoggerFactory.getLogger(BackupController.class);

	private @Autowired SystemSetupService demoService;
	private @Autowired JobService jobService;
	private @Autowired RoleDao roleDao;
	private @Autowired RegionDao regionDao;
	private @Autowired IndustryDao industryDao;
	private @Autowired JobCountPerDayDao jobCountPerDayDao;
	private @Autowired UserService userService;
	private @Autowired ServerSettings serverSettings;
	private @Autowired Jaxb2Marshaller marshaller;
	private @Autowired CommonsMultipartResolver multipartResolver;


	private static final long serialVersionUID = -3422780336408883930L;

	/**
	 * Provide a complete set of master data as XML document.
	 *
	 * @param model
	 * @param out
	 * @throws JAXBException
	 */
	@RequestMapping("/admin/backup.xml")
	public void backup(final ModelMap model, final OutputStream out) throws JAXBException {

		@InvUnk("Reassign") Backup backup = new Backup();
		@InvUnk("Dynamic dispatch") List<JobCountPerDay> l1 = jobCountPerDayDao.getAll();
		@InvUnk("Dynamic dispatch") List <Industry> l2 = jobService.getIndustries();
		@InvUnk("Dynamic dispatch") List<Region> l3 = jobService.getRegions();
		@InvUnk("Dynamic dispatch") List<Role> l4 = roleDao.getAll();
		@InvUnk("Dynamic dispatch") List<User> l5 = userService.getAllUsers();
		@InvUnk("Dynamic dispatch") List <Job> l6 = jobService.getJobs();
		backup.setJobCountPerDay(l1);
		backup.setIndustries(l2);
		backup.setRegions(l3);
		backup.setRoles(l4);
		backup.setUsers(l5);
		backup.setJobs(l6);

		marshaller.marshal(backup, new StreamResult(out));

	}

	/**
	 * Render the restore screen, where the user can upload a data file
	 * to restore master data.
	 *
	 * @return
	 * @throws JAXBException
	 * @throws IOException
	 */
	@RequestMapping(value="/admin/restore", method = RequestMethod.GET)
	public String restore() throws JAXBException, IOException {
		return "admin/restore";
	}

	/**
	 * Perform the master data restore operation (the user has provided a
	 * file and posted the file to the server).
	 *
	 *
	 * @param file The file to restore
	 * @param result Validation issues
	 * @return The view to return to.
	 * @throws JAXBException
	 * @throws IOException
	 */
	@Transactional
	@RequestMapping(value="/admin/restore", method = RequestMethod.POST)
	public String restore(final @RequestParam("file") MultipartFile file,
						  final BindingResult result) throws JAXBException, IOException {

		if (!file.isEmpty()) {
			demoService.restore(file.getInputStream());
		} else {
			result.reject("class.backupcontroller.validation.file.empty");
		}

		return "redirect:../../admin/index.html";

	}

}
