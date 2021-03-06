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
package org.jrecruiter.web.views;

import java.util.List;
import java.util.Map;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamWriter;

import org.jrecruiter.common.CalendarUtils;
import org.jrecruiter.model.Job;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.web.servlet.View;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

/**
 * Provides an XML document containing jobs, suitable for Indeed.com integration.
 *
 * @author Gunnar Hillert
 */
public class XmlView implements View {

	public static final Logger LOGGER = LoggerFactory.getLogger(XmlView.class);

	/* (non-Javadoc)
	 * @see org.springframework.web.servlet.View#getContentType()
	 */
	@Override
	public String getContentType() {
		return "text/xml";
	}

	/* (non-Javadoc)
	 * @see org.springframework.web.servlet.View#render(java.util.Map, javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse)
	 */
	@Override
	public void render(final Map model,
					   final HttpServletRequest request,
					   final HttpServletResponse response) throws Exception {

		response.setContentType(this.getContentType());

		XMLOutputFactory outputFactory = XMLOutputFactory.newInstance();
		XMLStreamWriter writer = outputFactory.createXMLStreamWriter(response.getOutputStream(), "UTF-8");

		writer.writeStartDocument("UTF-8", "1.0");

		writer.writeStartElement("source");
		writer.writeStartElement("publisher");
		writer.writeCData("jRecruiter - AJUG Job Postings");
		writer.writeEndElement();

		writer.writeStartElement("publisherUrl");
		writer.writeCData("http://www.ajug.org/jobs/");
		writer.writeEndElement();

		writer.writeStartElement("lastBuildDate");
		writer.writeCharacters(CalendarUtils.getXmlFormatedDate());
		writer.writeEndElement();

		final String serverAddress = (String) model.get("serverAddress");

		int i = 0;

		for (final Job job : (List<Job>) model.get("jobs")) {

			writer.writeStartElement("job");

			writer.writeStartElement("jobTitle");
			writer.writeCData(job.getJobTitle());
			writer.writeEndElement();

			writer.writeStartElement("date");
			writer.writeCData(CalendarUtils.getXmlFormatedDate(job.getUpdateDate()));
			writer.writeEndElement();

			writer.writeStartElement("referenceNumber");
			writer.writeCData(String.valueOf(job.getId()));
			writer.writeEndElement();

			writer.writeStartElement("url");

			final String jobUrl = serverAddress + "/job-detail.html?jobId=" + job.getId();

			writer.writeCData(jobUrl);
			writer.writeEndElement();

			writer.writeStartElement("company");
			writer.writeCData(job.getBusinessName());
			writer.writeEndElement();

			writer.writeStartElement("city");
			writer.writeCData(job.getBusinessCity());
			writer.writeEndElement();

			writer.writeStartElement("state");
			writer.writeCData(job.getBusinessState());
			writer.writeEndElement();

			writer.writeStartElement("country");
			writer.writeCData("US");
			writer.writeEndElement();

			writer.writeStartElement("postalCode");
			writer.writeCData(job.getBusinessZip());
			writer.writeEndElement();

			writer.writeStartElement("description");
			writer.writeCData(job.getDescription());
			writer.writeEndElement();

			writer.writeStartElement("education");
			writer.writeCData("");
			writer.writeEndElement();

			writer.writeStartElement("salary");
			writer.writeCData(String.valueOf(job.getSalary()));
			writer.writeEndElement();

			writer.writeStartElement("jobtype");
			writer.writeCData("");
			writer.writeEndElement();

			writer.writeStartElement("category");
			writer.writeCData(job.getIndustry().getName());
			writer.writeEndElement();

			writer.writeStartElement("experience");
			writer.writeCData("");
			writer.writeEndElement();

			writer.writeEndElement();

			if (job.getId().equals(Long.valueOf(3520))) {
				LOGGER.info("1");
			}

			if (i % 300 == 0) {
				writer.flush();
			}

			i++;

		}

		writer.writeEndDocument();
		writer.flush();
		writer.close();

	}

}
