INSERT INTO jforum_categories (category_id, category_title, category_order, category_moderated) VALUES (1, 'c1', 0, 0)
INSERT INTO jforum_forums (forum_id, category_id, forum_name, forum_order, forum_moderated) VALUES (1, 1, 'f1.1', 0, 0)
INSERT INTO jforum_forums (forum_id, category_id, forum_name, forum_order, forum_moderated) VALUES (2, 1, 'f1.2', 0, 0)
INSERT INTO jforum_users (user_id, username, user_password, user_email, user_active, USER_ATTACHSIG, USER_ALLOWAVATAR, USER_ALLOWBBCODE, USER_ALLOWHTML, DELETED, USER_NOTIFY_ALWAYS, USER_NOTIFY_PM, USER_ALLOW_PM, RANK_ID, USER_ALLOWSMILIES, USER_POSTS, USER_VIEWEMAIL, USER_ALLOW_VIEWONLINE, USER_NOTIFY_TEXT, user_notify) VALUES (1, 'u1', 'x', 'y', 0, 0, 0, 0, 0, 0, 0, 0, 0, null, 0, 0, 0, 0, 0, 0)

INSERT INTO jforum_topics (topic_id, forum_id, topic_subject, user_id, topic_date, TOPIC_STATUS, TOPIC_REPLIES, TOPIC_VIEWS, TOPIC_TYPE, TOPIC_VOTE_ID, topic_moved_id, need_moderate, has_attachment) VALUES (1, 1, 't1.1', 1, CURRENT_TIMESTAMP, 0, 0, 0, 0, null, 0, 0,false)
INSERT INTO jforum_topics (topic_id, forum_id, topic_subject, user_id, topic_date, TOPIC_STATUS, TOPIC_REPLIES, TOPIC_VIEWS, TOPIC_TYPE, TOPIC_VOTE_ID, topic_moved_id, need_moderate, has_attachment) VALUES (2, 2, 't2.1', 1, CURRENT_TIMESTAMP, 0, 0, 0, 0, null, 1, 0,false)
INSERT INTO jforum_topics (topic_id, forum_id, topic_subject, user_id, topic_date, TOPIC_STATUS, TOPIC_REPLIES, TOPIC_VIEWS, TOPIC_TYPE, TOPIC_VOTE_ID, topic_moved_id, need_moderate, has_attachment) VALUES (3, 2, 't2.2', 1, CURRENT_TIMESTAMP, 0, 0, 0, 0, null, 0, 0,false)

INSERT INTO jforum_posts (post_id, topic_id, user_id, post_date, need_moderate, enable_bbcode, post_edit_count, attach, enable_html, enable_sig, enable_smilies, forum_id) VALUES (1, 1, 1, '2008-06-11 14:54:32', 0, 0, 0, 0, 0, 0, 0, 1)
INSERT INTO jforum_posts (post_id, topic_id, user_id, post_date, need_moderate, enable_bbcode, post_edit_count, attach, enable_html, enable_sig, enable_smilies, forum_id) VALUES (2, 2, 1, '2008-06-11 14:54:33', 0, 0, 0, 0, 0, 0, 0, 2)
INSERT INTO jforum_posts (post_id, topic_id, user_id, post_date, need_moderate, enable_bbcode, post_edit_count, attach, enable_html, enable_sig, enable_smilies, forum_id) VALUES (3, 3, 1, '2008-06-11 14:54:33', 1, 0, 0, 0, 0, 0, 0, 2)

UPDATE jforum_topics SET topic_first_post_id = 1, topic_last_post_id = 1 WHERE topic_id = 1
UPDATE jforum_topics SET topic_first_post_id = 2, topic_last_post_id = 2 WHERE topic_id = 2
UPDATE jforum_topics SET topic_first_post_id = 3, topic_last_post_id = 3 WHERE topic_id = 3