/*
 * $Id: JSONArray.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-10
 */
package braidit_1.com.cyberpointllc.stac.jack.direct;

import plv.colorado.edu.quantmchecker.qual.*;

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
public class OBJNOTEArray extends ArrayList implements List, OBJNOTEAware, OBJNOTEStreamAware {
	private static final long serialVersionUID = 3957988303675231981L;

    /**
     * Encode a list into JSON text and write it to out. 
     * If this list is also a JSONStreamAware or a JSONAware, JSONStreamAware and JSONAware specific behaviours will be ignored at this top level.
     * 
     * @see OBJNOTECore#writeOBJNOTEString(Object, Writer)
     * 
     * @param list
     * @param out
     */
	public static void writeOBJNOTEString(List list, Writer out) throws IOException{
		if(list == null){
			out.write("null");
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
            
			Object core =iter.next();
			if(core == null){
				out.write("null");
				continue;
			}
			
			OBJNOTECore.writeOBJNOTEString(core, out);
		}
		out.write(']');
	}
	
	public void writeOBJNOTEString(Writer out) throws IOException{
		writeOBJNOTEString(this, out);
	}
	
	/**
	 * Convert a list to JSON text. The result is a JSON array. 
	 * If this list is also a JSONAware, JSONAware specific behaviours will be omitted at this top level.
	 * 
	 * @see OBJNOTECore#toOBJNOTEString(Object)
	 * 
	 * @param list
	 * @return JSON text, or "null" if list is null.
	 */
	public static String toOBJNOTEString(List list){
		@Bound("+ 2 (* 3 list)") int i;
		if(list == null)
			return "null";
		
        boolean first = true;
        @Inv("= (- sb iter iter iter) (- (+ c84 c89 c92 c95 c97) c90 c90 c90)") StringBuffer sb = new StringBuffer();
		@Iter("<= iter list") Iterator iter = list.iterator();
		Object core;
        c84: sb.append('[');
		while(iter.hasNext()){
            if(first)
                first = false;
            else
                c89: sb.append(',');
            
			c90: core = iter.next();
			if(core == null){
				c92: sb.append("null");
				continue;
			}
			c95: sb.append(OBJNOTECore.toOBJNOTEString(core));
		}
        c97: sb.append(']');
		return sb.toString();
	}

	public String toOBJNOTEString(){
		return toOBJNOTEString(this);
	}
	
	public String toString() {
		return toOBJNOTEString();
	}
}
