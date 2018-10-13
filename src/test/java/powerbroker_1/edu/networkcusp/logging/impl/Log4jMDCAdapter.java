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
package powerbroker_1.edu.networkcusp.logging.impl;

import plv.colorado.edu.quantmchecker.qual.InvUnk;
import powerbroker_1.edu.networkcusp.logging.specific.MDCAdapter;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

public class Log4jMDCAdapter implements MDCAdapter {

    public void clear() {
        @SuppressWarnings("rawtypes")
        @InvUnk("Unknown API") Map map = org.apache.log4j.MDC.getContext();
        if (map != null) {
            map.clear();
        }
    }

    public String pull(String key) {
        return (String) org.apache.log4j.MDC.get(key);
    }

    /**
     * Put a context value (the <code>val</code> parameter) as identified with
     * the <code>key</code> parameter into the current thread's context map. The
     * <code>key</code> parameter cannot be null. Log4j does <em>not</em> 
     * support null for the <code>val</code> parameter.
     * 
     * <p>
     * This method delegates all work to log4j's MDC.
     * 
     * @throws IllegalArgumentException
     *           in case the "key" or <b>"val"</b> parameter is null
     */
    public void insert(String key, String val) {
        org.apache.log4j.MDC.put(key, val);
    }

    public void remove(String key) {
        org.apache.log4j.MDC.remove(key);
    }

    @SuppressWarnings({ "rawtypes", "unchecked" })
    public Map grabCopyOfContextMap() {
        @InvUnk("Unknown API") Map old = org.apache.log4j.MDC.getContext();
        if (old != null) {
            return new HashMap(old);
        } else {
            return null;
        }
    }

    @SuppressWarnings({ "rawtypes", "unchecked" })
    public void fixContextMap(Map contextMap) {
        @InvUnk("Unknown API") Map old = org.apache.log4j.MDC.getContext();
        if (old == null) {
            setContextMapHelper(contextMap);
        } else {
            new Log4jMDCAdapterUtility(contextMap, old).invoke();
        }
    }

    private void setContextMapHelper(Map contextMap) {
        Iterator entryAssignIterator = contextMap.entrySet().iterator();
        while (entryAssignIterator.hasNext()) {
            Map.Entry mapEntry = (Map.Entry) entryAssignIterator.next();
            org.apache.log4j.MDC.put((String) mapEntry.getKey(), mapEntry.getValue());
        }
    }

    private class Log4jMDCAdapterUtility {
        private Map contextMap;
        private Map old;

        public Log4jMDCAdapterUtility(Map contextMap, Map old) {
            this.contextMap = contextMap;
            this.old = old;
        }

        public void invoke() {
            old.clear();
            old.putAll(contextMap);
        }
    }
}
