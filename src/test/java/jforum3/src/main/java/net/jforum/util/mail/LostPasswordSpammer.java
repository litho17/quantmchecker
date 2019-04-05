/*
 * Copyright (c) JForum Team
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms,
 * with or without modification, are permitted provided
 * that the following conditions are met:
 *
 * 1) Redistributions of source code must retain the above
 * copyright notice, this list of conditions and the
 * following  disclaimer.
 * 2)  Redistributions in binary form must reproduce the
 * above copyright notice, this list of conditions and
 * the following disclaimer in the documentation and/or
 * other materials provided with the distribution.
 * 3) Neither the name of "Rafael Steil" nor
 * the names of its contributors may be used to endorse
 * or promote products derived from this software without
 * specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT
 * HOLDERS AND CONTRIBUTORS "AS IS" AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING,
 * BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
 * THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER
 * IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE
 *
 * This file creation date: 19/04/2004 - 21:11:42
 * The JForum Project
 * http://www.jforum.net
 */
package net.jforum.util.mail;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.jforum.core.exceptions.MailException;
import net.jforum.entities.User;
import net.jforum.util.ConfigKeys;
import net.jforum.util.JForumConfig;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;


/**
 * Send an email for lost password requests
 *
 * @author Rafael Steil
 */
public class LostPasswordSpammer extends Spammer {
	public LostPasswordSpammer(JForumConfig config) throws MailException {
		super(config);
	}

	public void prepare(User user, String mailSubject) {
		@Bound("7") int i;
		@Inv("= sb (+ c68 c69 c70 c71)") StringBuilder sb = new StringBuilder();
		c68: sb.append(this.buildForumLink());
		c69: sb.append("user/recoverPassword/");
		c70: sb.append(user.getActivationKey());
		c71: sb.append(this.getConfig().getValue(ConfigKeys.SERVLET_EXTENSION));
		String url = sb.toString();

		@Inv("= params (+ c75 c76)") Map<String, Object> params = new HashMap<String, Object>();
		c75: params.put("url", url);
		c76: params.put("user", user);

		@Inv("= recipients c79") List<User> recipients = new ArrayList<User>();
		c79: recipients.add(user);

		this.setUsers(recipients);
		this.setTemplateParams(params);

		super.prepareMessage(mailSubject, this.getConfig().getValue(ConfigKeys.MAIL_LOST_PASSWORD_MESSAGE_FILE));
	}
}