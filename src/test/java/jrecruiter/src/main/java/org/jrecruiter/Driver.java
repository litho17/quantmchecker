package org.jrecruiter;

import org.jrecruiter.web.actions.*;
import org.jrecruiter.web.actions.admin.BackupController;
import org.jrecruiter.web.actions.admin.SystemInformationController;
import org.jrecruiter.web.actions.registration.AccountVerificationAction;
import org.springframework.ui.Model;
import org.springframework.ui.ModelMap;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

import javax.servlet.ServletContext;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpSession;
import javax.servlet.http.HttpSessionContext;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.List;

/**
 * @author Tianhan Lu
 */
public class Driver {
    Model model;
    public void main(List<Object> input) throws Exception {
        IndeedController indeedController = null;
        LoginAction loginAction = null;
        AccountVerificationAction accountVerificationAction = null;
        SystemInformationController systemInformationController = null;
        BackupController backupController = null;
        JobDetailController jobDetailController = null;
        ShowJobsController showJobsController = null;
        HttpServletRequest request = null;
        LogoutController logoutController = null;
        SetupApiKeysController setupApiKeysController = null;
        IndexController indexController = null;
        Object o;
        @Bound("3") int b;
        @Inv("= map (- (* 3 c43) c44 c44 c44)") ModelMap map = null;
        Iterator<Object> it = input.iterator();
        while (true) {
            c42: o = it.next();
            c43: showJobsController.execute(map, request, false);
            c44: map.remove(request);
            indeedController.execute(map);
            loginAction.execute();
            accountVerificationAction.execute();
            systemInformationController.execute(map);
            backupController.restore();
            jobDetailController.execute(0L, "", map, new HttpSession() {
                @Override
                public long getCreationTime() {
                    return 0;
                }

                @Override
                public String getId() {
                    return null;
                }

                @Override
                public long getLastAccessedTime() {
                    return 0;
                }

                @Override
                public ServletContext getServletContext() {
                    return null;
                }

                @Override
                public void setMaxInactiveInterval(int i) {

                }

                @Override
                public int getMaxInactiveInterval() {
                    return 0;
                }

                @Override
                public HttpSessionContext getSessionContext() {
                    return null;
                }

                @Override
                public Object getAttribute(String s) {
                    return null;
                }

                @Override
                public Object getValue(String s) {
                    return null;
                }

                @Override
                public Enumeration<String> getAttributeNames() {
                    return null;
                }

                @Override
                public String[] getValueNames() {
                    return new String[0];
                }

                @Override
                public void setAttribute(String s, Object o) {

                }

                @Override
                public void putValue(String s, Object o) {

                }

                @Override
                public void removeAttribute(String s) {

                }

                @Override
                public void removeValue(String s) {

                }

                @Override
                public void invalidate() {

                }

                @Override
                public boolean isNew() {
                    return false;
                }
            });
            indexController.execute(model);
            logoutController.execute();
            setupApiKeysController.execute(map);
            indeedController.execute(map);
        }
    }
}
