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
package net.jforum.util.mail;

import java.text.MessageFormat;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.jforum.core.exceptions.MailException;
import net.jforum.entities.Topic;
import net.jforum.entities.User;
import net.jforum.entities.util.Pagination;
import net.jforum.util.ConfigKeys;
import net.jforum.util.JForumConfig;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

/**
 * Notify users of replies to topics they are watching
 *
 * @author Rafael Steil
 */
public class TopicReplySpammer extends Spammer {
	public TopicReplySpammer(JForumConfig config) throws MailException {
		super(config);
	}

	/**
	 * Creates a new instance with a message's contents send
	 *
	 * @param topic the topic we are replying to
	 * @param post the post instance, with the message's contents. If null, only a notification will be sent
	 * @param users list of users who'll be notified
	 */
	public void prepare(Topic topic, List<User> users) {
		int postsPerPage = this.getConfig().getInt(ConfigKeys.POSTS_PER_PAGE);

		@InvUnk("Extend library class") Pagination pagination = new Pagination(this.getConfig(), 0).forTopic(topic);

		String page = "";

		if (topic.getTotalReplies() >= postsPerPage) {
			page = pagination.getStart() + "/";
		}

		String forumLink = this.buildForumLink();

		String path = this.buildMessageLink(topic, page, forumLink);
		String unwatch = this.buildUnwatchLink(topic, forumLink);

		@Bound("3") int i;
		@Inv("= params (+ c61 c62 c63)") Map<String, Object> params = new HashMap<String, Object>();

		c61: params.put("topic", topic);
		c62: params.put("path", path);
		c63: params.put("unwatch", unwatch);

		this.setUsers(users);
		this.setTemplateParams(params);

		String subject = this.getConfig().getValue(ConfigKeys.MAIL_NEW_ANSWER_SUBJECT);

		this.prepareMessage(MessageFormat.format(subject, topic.getSubject()),
			this.getConfig().getValue(ConfigKeys.MAIL_NEW_ANSWER_MESSAGE_FILE));
	}

	/**
	 * Creates the "unwatch" link for the current topic
	 *
	 * @param topic the topic
	 * @param forumLink the forum's link
	 * @return the unwath link
	 */
	private String buildUnwatchLink(Topic topic, String forumLink) {
		@Bound("4") int i;
		@Inv("= sb (+ c83 c84 c85 c86)") StringBuilder sb = new StringBuilder(128);
		c83: sb.append(forumLink);
		c84: sb.append("topics/unwatch/");
		c85: sb.append(topic.getId());
		c86: sb.append(this.getConfig().getValue(ConfigKeys.SERVLET_EXTENSION));
		return sb.toString();
	}

	/**
	 * Creates the link to read the message online
	 *
	 * @param topic the topic
	 * @param page the current topic's page
	 * @param forumLink the forum's link
	 * @return the link to the message
	 */
	private String buildMessageLink(Topic topic, String page, String forumLink) {
		@Bound("7") int i;
		@Inv("= sb (+ c100 c101 c102 c103 c104 c105 c106)") StringBuilder sb = new StringBuilder(128);
		c100: sb.append(forumLink);
		c101: sb.append("topics/list/");
		c102: sb.append(page);
		c103: sb.append(topic.getId());
		c104: sb.append(this.getConfig().getValue(ConfigKeys.SERVLET_EXTENSION));
		c105: sb.append('#');
		c106: sb.append(topic.getLastPost().getId());
		return sb.toString();
	}
}
