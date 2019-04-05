package net.jforum;

import net.jforum.controllers.*;
import net.jforum.entities.User;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.Iterator;
import java.util.List;

/**
 * @author Tianhan Lu
 */
public class Driver {
    public void main(List<Object> input) throws Exception {
        AdminController adminController = null;
        GroupAdminController groupAdminController = null;
        AvatarAdminController avatarAdminController = null;
        BadWordAdminController badWordAdminController = null;
        BanlistAdminController banlistAdminController = null;
        CategoryAdminController categoryAdminController = null;
        UserController userController = null;
        ForumAdminController forumAdminController = null;
        HibernateStatisticsController hibernateStatisticsController = null;
        ModerationController moderationController = null;
        LuceneAdminController luceneAdminController = null;
        PostController postController = null;
        PrivateMessageController privateMessageController = null;
        RankingAdminController rankingAdminController = null;
        RecentTopicsController recentTopicsController = null;
        RSSController rssController = null;
        SearchController searchController = null;
        SmilieAdminController smilieAdminController = null;
        ThemeController themeController = null;
        TopicController topicController = null;
        UserAdminController userAdminController = null;
        @Inv("= (- messageController.i18n.messages it) (- c48 c44)") MessageController messageController = null;
        @Inv("= (- configController.service.i18n.messages it) (- c49 c44)") ConfigController configController = null;
        @Inv("and (= (- user.groups it) (- c47 c44)) (= user.avatar.users 0) (= user.posts 0)") User user = new User();
        Object o;
        @Bound("* 3 input")
        @Iter("<= it input") Iterator<Object> it = input.iterator();
        while (true) {
            c44: o = it.next();
            c47: userController.insertSave(user);
            c48: messageController.accessDenied();
            c49: configController.save();
            adminController.main();
            groupAdminController.add();
            avatarAdminController.add();
            badWordAdminController.add();
            banlistAdminController.list();
            categoryAdminController.add();
            forumAdminController.add();
            hibernateStatisticsController.list();
            moderationController.showActivityLog(0);
            luceneAdminController.list();
            postController.delete(0);
            privateMessageController.send();
            rankingAdminController.add();
            recentTopicsController.list();
            rssController.forumTopics(0);
            searchController.filters();
            smilieAdminController.add();
            themeController.add();
            topicController.add(0);
            userAdminController.edit(0);
        }
    }
}
