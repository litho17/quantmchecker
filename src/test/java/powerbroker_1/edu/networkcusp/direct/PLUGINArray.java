/*
 * $Id: JSONArray.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-10
 */
package powerbroker_1.edu.networkcusp.direct;

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
public class PLUGINArray extends ArrayList implements List, PLUGINAware, PLUGINStreamAware {
	private static final long serialVersionUID = 3957988303675231981L;

    /**
     * Encode a list into JSON text and write it to out. 
     * If this list is also a JSONStreamAware or a JSONAware, JSONStreamAware and JSONAware specific behaviours will be ignored at this top level.
     * 
     * @see PLUGINDetail#writePLUGINString(Object, Writer)
     *
     * @param list
     * @param out
     */
	public static void writePLUGINString(List list, Writer out) throws IOException{
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

			Object detail =iter.next();
			if(detail == null){
				out.write("null");
				continue;
			}

			PLUGINDetail.writePLUGINString(detail, out);
		}
		out.write(']');
	}

	public void writePLUGINString(Writer out) throws IOException{
		writePLUGINString(this, out);
	}

	/**
	 * Convert a list to JSON text. The result is a JSON array.
	 * If this list is also a JSONAware, JSONAware specific behaviours will be omitted at this top level.
	 *
	 * @see PLUGINDetail#toPLUGINString(Object)
	 * 
	 * @param list
	 * @return JSON text, or "null" if list is null.
	 */
	public static String toPLUGINString(List list){
		if(list == null)
			return "null";
		@Bound("+ 2 (* 3 list)") int i;
        boolean first = true;
        @Inv("= (- sb iter iter iter) (- (+ c82 c88 c92 c95 c97) c90 c90 c90)") StringBuffer sb = new StringBuffer();
		@Iter("<= iter list") Iterator iter=list.iterator();
        
        c82: sb.append('[');
		while(iter.hasNext()){
            if(first)
                first = false;
            else
                c88: sb.append(',');
			Object detail;
			c90: detail = iter.next();
			if(detail == null){
				c92: sb.append("null");
				continue;
			}
			c95: sb.append(PLUGINDetail.toPLUGINString(detail));
		}
        c97: sb.append(']');
		return sb.toString();
	}

	public String toPLUGINString(){
		return toPLUGINString(this);
	}
	
	public String toString() {
		return toPLUGINString();
	}

	
		
}
