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
package net.jforum.services;

import java.util.ArrayList;
import java.util.Date;
import java.util.Iterator;
import java.util.List;

import net.jforum.entities.Poll;
import net.jforum.entities.PollOption;
import net.jforum.entities.Topic;

import org.apache.commons.lang.StringUtils;

import br.com.caelum.vraptor.ioc.Component;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

/**
 * @author Rafael Steil
 */
@Component
public class PollService {
	public void processChanges(Poll originalPoll, List<PollOption> options) {
		for (PollOption option : options) {
			if (option.getId() == 0) {
				options.add(option);
				option.setPoll(originalPoll);
			}
			else {
				PollOption originalOption = this.findOption(option.getId(), originalPoll.getOptions());

				if (originalOption != null && !StringUtils.isEmpty(option.getText())
						&& !originalOption.getText().equals(option.getText())) {
					originalOption.setText(option.getText());
				}
			}
		}

		originalPoll.getOptions().addAll(options);

		for (Iterator<PollOption> iterator = originalPoll.getOptions().iterator(); iterator.hasNext(); ) {
			PollOption currentOption = iterator.next();

			if (this.findOption(currentOption.getId(), options) == null) {
				iterator.remove();
			}
		}
	}

	private PollOption findOption(int optionId, List<PollOption> options) {
		for (PollOption option : options) {
			if (option.getId() == optionId) {
				return option;
			}
		}

		return null;
	}

	public void associatePoll(Topic topic, List<PollOption> pollOptions) {
		if (topic.getPoll() == null) {
			return;
		}

		if (StringUtils.isEmpty(topic.getPoll().getLabel()) || pollOptions == null) {
			topic.setPoll(null);
			return;
		}

		topic.getPoll().setStartDate(new Date());

		for (Iterator<PollOption> iterator = pollOptions.iterator(); iterator.hasNext();) {
			PollOption option = iterator.next();

			if (StringUtils.isEmpty(option.getText())) {
				iterator.remove();
			}
			else {
				option.setPoll(topic.getPoll());
			}
		}

		if (pollOptions.size() == 0) {
			topic.setPoll(null);
		}
		else {
			topic.getPoll().setOptions(pollOptions);
		}
	}
}
