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

import java.io.IOException;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;

import javax.servlet.http.HttpServletRequest;

import br.com.caelum.vraptor.interceptor.multipart.UploadedFile;
import net.jforum.actions.helpers.ActionUtils;
import net.jforum.actions.helpers.Actions;
import net.jforum.actions.helpers.AttachedFile;
import net.jforum.actions.helpers.Domain;
import net.jforum.actions.helpers.PostFormOptions;
import net.jforum.core.SecurityConstraint;
import net.jforum.core.exceptions.ForumException;
import net.jforum.entities.*;
import net.jforum.entities.util.Pagination;
import net.jforum.repository.PostRepository;
import net.jforum.repository.SmilieRepository;
import net.jforum.security.ChangePostRule;
import net.jforum.security.RoleManager;
import net.jforum.services.AttachmentService;
import net.jforum.services.PostService;
import net.jforum.util.JForumConfig;
import net.jforum.util.URLBuilder;
import br.com.caelum.vraptor.Path;
import br.com.caelum.vraptor.Resource;
import br.com.caelum.vraptor.Result;
import net.jforum.util.UploadUtils;
import org.apache.commons.lang.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;

/**
 * @author Rafael Steil
 */
@Resource
@Path(Domain.POSTS)
public class PostController {
	private PostRepository postRepository;
	private SmilieRepository smilieRepository;
	private PostService postService;
	private JForumConfig config;
	private UserSession userSession;
	private AttachmentService attachmentService;
	private HttpServletRequest request;
	private final Result result;

	public PostController(PostRepository postRepository, SmilieRepository smilieRepository,
			PostService postService, JForumConfig config, UserSession userSession,
		AttachmentService attachmentService, HttpServletRequest request, Result result) {
		this.postRepository = postRepository;
		this.smilieRepository = smilieRepository;
		this.postService = postService;
		this.config = config;
		this.userSession = userSession;
		this.attachmentService = attachmentService;
		this.request = request;
		this.result = result;
	}

	/**
	 * Deletes an existing post
	 * @param postId
	 */
	@SecurityConstraint(value = ChangePostRule.class)
	public void delete(int postId) {
		Post post = this.postRepository.get(postId);
		Topic topic = post.getTopic();
		this.postService.delete(post);

		if (topic.getTotalPosts() > 0) {
			this.redirecToListing(topic);
		}
		else {
			//TODO pass zero?
			this.result.redirectTo(ForumController.class).show(topic.getForum().getId(), 0);
		}
	}

	/**
	 * Saves an existing message
	 * @param post the message to save
	 * @param postOptions the formatting options
	 */
	@SecurityConstraint(value = ChangePostRule.class)
	public void editSave( Post post,  PostFormOptions postOptions, List<PollOption> pollOptions,  ModerationLog moderationLog) {
		@Bound("total_attachments") int j;
		ActionUtils.definePostOptions(post, postOptions);
		post.getTopic().setType(postOptions.getTopicType());

		Post currentPost = this.postRepository.get(post.getId());
		@Inv("= (- attachments i) (- c115 c117)") List<AttachedFile> attachments = new ArrayList<AttachedFile>();

		RoleManager roleManager = this.userSession.getRoleManager();

		if (roleManager.isAttachmentsAlllowed(currentPost.getForum().getId())) {
			String t = request.getParameter("total_attachments");
			// List<AttachedFile> attachedFiles = new ArrayList<AttachedFile>();

			if (StringUtils.isEmpty(t)) {
				helper(roleManager, pollOptions, moderationLog, post, attachments);
				return;
			}

			int total = Integer.parseInt(t);

			if (total < 1) {
				helper(roleManager, pollOptions, moderationLog, post, attachments);
				return;
			}

			long totalSize = 0;

			@Iter("<= i total_attachments") int i = 0;
			for (; i < total;) {
				UploadedFile fileInfo = (UploadedFile) request.getAttribute("attachment_" + i);

				if (fileInfo == null) {
					continue;
				}

				if (fileInfo.getFileName().indexOf('\000') > -1) {
					AttachmentService.logger.warn("Possible bad attachment (null char): " + fileInfo.getFileName());
					continue;
				}

				UploadUtils uploadUtils = new UploadUtils(fileInfo);
				String description = request.getParameter("attachment_description_" + i);

				Attachment attachment = new Attachment();
				try {
					attachment.setFilesize(fileInfo.getFile().available());
				} catch (IOException e) {
					throw new ForumException(e);
				}
				attachment.setDescription(description);
				attachment.setMimetype(fileInfo.getContentType());

				// Get only the filename, without the path (IE does that)
				String realName = attachmentService.stripPath(fileInfo.getFileName());

				attachment.setRealFilename(realName);
				attachment.setUploadDate(new Date());

				attachment.setFileExtension(uploadUtils.getExtension());

				String savePath = attachmentService.buildStoreFilename(attachment);
				attachment.setPhysicalFilename(savePath);

				c115: attachments.add(new AttachedFile(attachment, uploadUtils));
				totalSize += attachment.getFilesize();
				c117: i = i + 1;
			}
			// attachments = this.attachmentService.processNewAttachments(this.request);
			this.attachmentService.editAttachments(currentPost, request);
		}
		helper(roleManager, pollOptions, moderationLog, post, attachments);
	}

	private void helper(RoleManager roleManager, List<PollOption> pollOptions, ModerationLog moderationLog, Post post, List<AttachedFile> attachments) {
		if (!roleManager.getCanCreatePolls()) {
			pollOptions = new ArrayList<PollOption>();
		}

		if (moderationLog != null) {
			moderationLog.setUser(this.userSession.getUser());
		}

		this.postService.update(post, roleManager.getCanCreateStickyAnnouncementTopics(), pollOptions, attachments, moderationLog);
		this.result.redirectTo(TopicController.class).list(post.getTopic().getId(), 0, true);
	}

	/**
	 * Shows the page to edit an existing post
	 * @param postId the id of the post to edit
	 */
	@SecurityConstraint(value = ChangePostRule.class)
	public void edit(int postId) {
		Post post = this.postRepository.get(postId);

		this.result.include("isEdit", true);
		this.result.include("post", post);
		this.result.include("topic", post.getTopic());
		this.result.include("forum", post.getTopic().getForum());
		this.result.include("smilies", this.smilieRepository.getAllSmilies());

		this.result.forwardTo(TopicController.class).add(0);

	}

	private void redirecToListing(Topic topic) {
		@InvUnk("Extend library class") Pagination pagination = new Pagination(this.config, 0).forTopic(topic);

		String url;
		if(pagination.getTotalPages() > 1) {
			url = URLBuilder.build(Domain.TOPICS, Actions.LIST, pagination.getTotalPages(), topic.getId());
		} else {
			url = URLBuilder.build(Domain.TOPICS, Actions.LIST, topic.getId());
		}

		this.result.redirectTo(url);
	}
}
