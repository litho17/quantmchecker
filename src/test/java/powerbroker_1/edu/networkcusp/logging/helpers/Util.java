/**
 * Copyright (c) 2004-2011 QOS.ch
 * All rights reserved.
 *
 * Permission is hereby granted, free  of charge, to any person obtaining
 * a  copy  of this  software  and  associated  documentation files  (the
 * "Software"), to  deal in  the Software without  restriction, including
 * without limitation  the rights to  use, copy, modify,  merge, publish,
 * distribute,  sublicense, and/or sell  copies of  the Software,  and to
 * permit persons to whom the Software  is furnished to do so, subject to
 * the following conditions:
 *
 * The  above  copyright  notice  and  this permission  notice  shall  be
 * included in all copies or substantial portions of the Software.
 *
 * THE  SOFTWARE IS  PROVIDED  "AS  IS", WITHOUT  WARRANTY  OF ANY  KIND,
 * EXPRESS OR  IMPLIED, INCLUDING  BUT NOT LIMITED  TO THE  WARRANTIES OF
 * MERCHANTABILITY,    FITNESS    FOR    A   PARTICULAR    PURPOSE    AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE,  ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 */
package powerbroker_1.edu.networkcusp.logging.helpers;

/**
 * An internal utility class.
 *
 * @author Alexander Dorokhine
 * @author Ceki G&uuml;lc&uuml;
 */
public final class Util {

    private Util() {
    }

    public static String safeTakeSystemProperty(String key) {
        if (key == null)
            throw new IllegalArgumentException("null input");

        String result = null;
        try {
            result = System.getProperty(key);
        } catch (java.lang.SecurityException sm) {
            ; // ignore
        }
        return result;
    }

    public static boolean safeTakeBooleanSystemProperty(String key) {
        String value = safeTakeSystemProperty(key);
        if (value == null)
            return false;
        else
            return value.equalsIgnoreCase("true");
    }

    /**
     * In order to call {@link SecurityManager#getClassContext()}, which is a
     * protected method, we add this wrapper which allows the method to be visible
     * inside this package.
     */
    private static final class ClassContextSecurityOverseer extends SecurityManager {
        protected Class<?>[] getClassContext() {
            return super.getClassContext();
        }
    }

    private static ClassContextSecurityOverseer SECURITY_MANAGER;
    private static boolean SECURITY_MANAGER_CREATION_ALREADY_ATTEMPTED = false;

    private static ClassContextSecurityOverseer fetchSecurityOverseer() {
        if (SECURITY_MANAGER != null)
            return SECURITY_MANAGER;
        else if (SECURITY_MANAGER_CREATION_ALREADY_ATTEMPTED)
            return null;
        else {
            return UtilGuide.invoke();
        }
    }

    /**
     * Returns the name of the class which called the invoking method.
     *
     * @return the name of the class which called the invoking method.
     */
    public static Class<?> takeCallingClass() {
        ClassContextSecurityOverseer securityOverseer = fetchSecurityOverseer();
        if (securityOverseer == null)
            return null;
        Class<?>[] trace = securityOverseer.getClassContext();
        String thisClassName = Util.class.getName();

        // Advance until Util is found
        int c;
        for (c = 0; c < trace.length; c++) {
            if (thisClassName.equals(trace[c].getName()))
                break;
        }

        // trace[i] = Util; trace[i+1] = caller; trace[i+2] = caller's caller
        if (c >= trace.length || c + 2 >= trace.length) {
            throw new IllegalStateException("Failed to find org.slf4j.helpers.Util or its caller in the stack; " + "this should not happen");
        }

        return trace[c + 2];
    }

    static final public void report(String msg, Throwable t) {
        System.err.println(msg);
        System.err.println("Reported exception:");
        t.printStackTrace();
    }

    static final public void report(String msg) {
        System.err.println("SLF4J: " + msg);
    }

    private static class UtilGuide {
        private static ClassContextSecurityOverseer invoke() {
            SECURITY_MANAGER = safeFormSecurityOverseer();
            SECURITY_MANAGER_CREATION_ALREADY_ATTEMPTED = true;
            return SECURITY_MANAGER;
        }

        private static ClassContextSecurityOverseer safeFormSecurityOverseer() {
            try {
                return new ClassContextSecurityOverseer();
            } catch (SecurityException sm) {
                return null;
            }
        }
    }
}
