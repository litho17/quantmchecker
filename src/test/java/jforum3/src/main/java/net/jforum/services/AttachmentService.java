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

import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Date;
import java.util.List;

import javax.servlet.http.HttpServletRequest;

import net.jforum.actions.helpers.AttachedFile;
import net.jforum.core.exceptions.ForumException;
import net.jforum.entities.Attachment;
import net.jforum.entities.Post;
import net.jforum.repository.AttachmentRepository;
import net.jforum.util.ConfigKeys;
import net.jforum.util.ImageUtils;
import net.jforum.util.JForumConfig;
import net.jforum.util.MD5;
import net.jforum.util.UploadUtils;

import org.apache.commons.lang.ArrayUtils;
import org.apache.commons.lang.StringUtils;
import org.apache.log4j.Logger;

import br.com.caelum.vraptor.interceptor.multipart.UploadedFile;
import br.com.caelum.vraptor.ioc.Component;
import plv.colorado.edu.quantmchecker.qual.*;

/**
 * @author Rafael Steil
 */
@Component
public class AttachmentService {
	public static Logger logger = Logger.getLogger(AttachmentService.class);

	private final JForumConfig config;
	private final AttachmentRepository repository;

	public AttachmentService(JForumConfig config, AttachmentRepository repository) {
		this.config = config;
		this.repository = repository;
	}

	public Attachment getAttachmentForDownload(int attachmentId) {
		Attachment attachment = this.repository.get(attachmentId);
		attachment.incrementDownloadCount();
		return attachment;
	}

	/**
	 * @param realName String
	 * @return String
	 */
	public String stripPath(String realName) {
		String separator = "/";
		int index = realName.lastIndexOf(separator);

		if (index == -1) {
			separator = "\\";
			index = realName.lastIndexOf(separator);
		}

		if (index > -1) {
			realName = realName.substring(index + 1);
		}

		return realName;
	}

	public void insertAttachments(List<AttachedFile> attachedFiles, Post post) {
		if (attachedFiles.size() > 0) {
			post.setHasAttachments(true);

			for (AttachedFile attachedFile : attachedFiles) {
				String path = this.config.getValue(ConfigKeys.ATTACHMENTS_STORE_DIR)
					+ "/" + attachedFile.getAttachment().getPhysicalFilename();

				attachedFile.getUploadUtils().saveUploadedFile(path);

				if (this.shouldCreateThumb(attachedFile.getAttachment())) {
					attachedFile.getAttachment().setHasThumb(true);
					this.createSaveThumb(path);
				}

				post.addAttachment(attachedFile.getAttachment());
			}
		}
	}

	private boolean shouldCreateThumb(Attachment attachment) {
		String extension = attachment.getFileExtension();

		return this.config.getBoolean(ConfigKeys.ATTACHMENTS_IMAGES_CREATE_THUMB)
			&& ("jpg".equals(extension) || "jpeg".equals(extension) || "gif".equals(extension) || "png".equals(extension));
	}

	private void createSaveThumb(String path) {
		try {
			BufferedImage image = ImageUtils.resizeImage(path, ImageUtils.IMAGE_JPEG,
				this.config.getInt(ConfigKeys.ATTACHMENTS_IMAGES_MAX_THUMB_W), this.config.getInt(ConfigKeys.ATTACHMENTS_IMAGES_MAX_THUMB_H));
			ImageUtils.saveImage(image, path + "_thumb", ImageUtils.IMAGE_JPEG);
		}
		catch (Exception e) {
			logger.error(e.toString(), e);
		}
	}

	public void editAttachments(Post post, HttpServletRequest request) {
		// Check for attachments to remove
		@InvUnk("Unknown API") List<String> deleteList = new ArrayList<String>();
		String[] delete = null;
		String s = request.getParameter("delete_attach");

		if (!StringUtils.isEmpty(s)) {
			delete = s.split(",");
		}

		if (!ArrayUtils.isEmpty(delete)) {
			for (String deleteId : delete) {
				if (!StringUtils.isEmpty(deleteId)) {
					int attachmentId = Integer.parseInt(deleteId);

					Attachment attachment = this.repository.get(attachmentId);
					post.getAttachments().remove(attachment);

					this.removeAttachmentFiles(attachment);
				}
			}

			deleteList = Arrays.asList(delete);
		}

		// Update
		String[] attachIds = null;
		s = request.getParameter("edit_attach_ids");
		if (!StringUtils.isEmpty(s)) {
			attachIds = s.split(",");
		}

		if (!ArrayUtils.isEmpty(attachIds)) {
			for (String x : attachIds) {
				if (deleteList.contains(x) || StringUtils.isEmpty(x)) {
					continue;
				}

				int attachmentId = Integer.parseInt(x);

				Attachment attachment = this.repository.get(attachmentId);
				attachment.setDescription(request.getParameter("edit_description_" + attachmentId));
			}
		}
	}

	public void deleteAllAttachments(Post post) {
		for (Attachment attachment : post.getAttachments()) {
			this.removeAttachmentFiles(attachment);
		}
	}

	private void removeAttachmentFiles(Attachment attachment) {
		String filename = this.buildDownloadPath(attachment);

		File f = new File(filename);

		if (f.exists()) {
			f.delete();
		}

		// Check if we have a thumb to delete
		f = new File(filename + "_thumb");

		if (f.exists()) {
			f.delete();
		}
	}

	public String buildStoreFilename(Attachment attachment) {
		int year = Calendar.getInstance().get(Calendar.YEAR);
		int month = Calendar.getInstance().get(Calendar.MONTH) + 1;
		int day = Calendar.getInstance().get(Calendar.DAY_OF_MONTH);

		@Bound("9") int i;
		@Inv("= dir (+ c258 c259 c260 c261 c262 c263 c267 c268 c269)") StringBuilder dir = new StringBuilder(256);
		c258: dir.append(year);
		c259: dir.append('/');
		c260: dir.append(month);
		c261: dir.append('/');
		c262: dir.append(day);
		c263: dir.append('/');

		new File(this.config.getValue(ConfigKeys.ATTACHMENTS_STORE_DIR) + "/" + dir).mkdirs();

		c267: dir.append(MD5.hash(attachment.getRealFilename() + System.currentTimeMillis()));
		c268: dir.append('.');
		c269: dir.append(attachment.getFileExtension());
		return dir.toString();
	}

	public String buildDownloadPath(Attachment attachment) {
		return String.format("%s/%s", this.config.getValue(ConfigKeys.ATTACHMENTS_STORE_DIR), attachment.getPhysicalFilename());
	}
}
