/*
 * $Id: JSONArray.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-10
 */
package withmi_1.edu.networkcusp.jackson.simple;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;


/**
 * A JSON array. JSONObject supports java.util.List interface.
 * 
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class JACKSONArray extends ArrayList implements List, JACKSONAware, JACKSONStreamAware {
	private static final long serialVersionUID = 3957988303675231981L;

    /**
     * Encode a list into JSON text and write it to out. 
     * If this list is also a JSONStreamAware or a JSONAware, JSONStreamAware and JSONAware specific behaviours will be ignored at this top level.
     * 
     * @see JACKSONValue#writeJACKSONString(Object, Writer)
     * 
     * @param list
     * @param out
     */
	public static void writeJACKSONString(List list, Writer out) throws IOException{
		if(list == null){
            writeJACKSONStringAdviser(out);
            return;
		}
		
		boolean first = true;
		Iterator iter=list.iterator();
		
        out.write('[');
		while(iter.hasNext()){
            if(first)
                first = false;
            else
                out.write(',');
            
			Object value=iter.next();
			if(value == null){
                writeJACKSONStringHelper(out);
                continue;
			}
			
			JACKSONValue.writeJACKSONString(value, out);
		}
		out.write(']');
	}

    private static void writeJACKSONStringHelper(Writer out) throws IOException {
        out.write("null");
        return;
    }

    private static void writeJACKSONStringAdviser(Writer out) throws IOException {
        new JACKSONArrayCoordinator(out).invoke();
        return;
    }

    public void writeJACKSONString(Writer out) throws IOException{
		writeJACKSONString(this, out);
	}
	
	/**
	 * Convert a list to JSON text. The result is a JSON array. 
	 * If this list is also a JSONAware, JSONAware specific behaviours will be omitted at this top level.
	 * 
	 * @see JACKSONValue#toJACKSONString(Object)
	 * 
	 * @param list
	 * @return JSON text, or "null" if list is null.
	 */
	public static String toJACKSONString(List list){
		if(list == null)
			return "null";
		
        boolean first = true;
        @Bound("+ 2 (* 3 list)") int i;
        @Inv("= (- sb iter iter iter) (- (+ c94 c99 c104 c106 c108) c102 c102 c102)") StringBuffer sb = new StringBuffer();
		@Iter("<= iter list") Iterator iter=list.iterator();
        
        c94: sb.append('[');
		while(iter.hasNext()){
            if(first)
                first = false;
            else
                c99: sb.append(',');
            
			Object value;
			c102: value=iter.next();
			if(value == null){
                c104: sb.append("null");
                continue;
			}
			c106: sb.append(JACKSONValue.toJACKSONString(value));
		}
        c108: sb.append(']');
		return sb.toString();
	}

    public String toJACKSONString(){
		return toJACKSONString(this);
	}
	
	public String toString() {
		return toJACKSONString();
	}


    private static class JACKSONArrayCoordinator {
        private Writer out;

        public JACKSONArrayCoordinator(Writer out) {
            this.out = out;
        }

        public void invoke() throws IOException {
            out.write("null");
            return;
        }
    }
}
