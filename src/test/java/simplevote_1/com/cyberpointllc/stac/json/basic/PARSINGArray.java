/*
 * $Id: JSONArray.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-10
 */
package simplevote_1.com.cyberpointllc.stac.json.basic;

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
public class PARSINGArray extends ArrayList implements List, PARSINGAware, PARSINGStreamAware {
	private static final long serialVersionUID = 3957988303675231981L;

    /**
     * Encode a list into JSON text and write it to out. 
     * If this list is also a JSONStreamAware or a JSONAware, JSONStreamAware and JSONAware specific behaviours will be ignored at this top level.
     * 
     * @see PARSINGEssence#writePARSINGString(Object, Writer)
     * 
     * @param list
     * @param out
     */
	public static void writePARSINGString(List list, Writer out) throws IOException{
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
            
			Object essence =iter.next();
			if(essence == null){
				new PARSINGArrayAid(out).invoke();
				continue;
			}
			
			PARSINGEssence.writePARSINGString(essence, out);
		}
		out.write(']');
	}

	public void writePARSINGString(Writer out) throws IOException{
		writePARSINGString(this, out);
	}
	
	/**
	 * Convert a list to JSON text. The result is a JSON array. 
	 * If this list is also a JSONAware, JSONAware specific behaviours will be omitted at this top level.
	 * 
	 * @see PARSINGEssence#toPARSINGString(Object)
	 * 
	 * @param list
	 * @return JSON text, or "null" if list is null.
	 */
	public static String toPARSINGString(List list){
		if(list == null)
			return "null";
		
        boolean first = true;
        StringBuffer sb = new StringBuffer();
		Iterator iter=list.iterator();
        
        sb.append('[');
		while(iter.hasNext()){
            if(first)
                first = false;
            else
                sb.append(',');
            
			Object essence =iter.next();
			if(essence == null){
				sb.append("null");
				continue;
			}
			sb.append(PARSINGEssence.toPARSINGString(essence));
		}
        sb.append(']');
		return sb.toString();
	}

	public String toPARSINGString(){
		return toPARSINGString(this);
	}
	
	public String toString() {
		return toPARSINGString();
	}


	private static class PARSINGArrayAid {
		private Writer out;

		public PARSINGArrayAid(Writer out) {
			this.out = out;
		}

		public void invoke() throws IOException {
			out.write("null");
			return;
		}
	}
}
