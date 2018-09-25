/*
 * $Id: ItemList.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-3-24
 */
package braidit_1.com.cyberpointllc.stac.jack.direct;

import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

/**
 * |a:b:c| => |a|,|b|,|c|
 * |:| => ||,||
 * |a:| => |a|,||
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class ItemList {
	private String sp=",";
	List items=new ArrayList();
	
	
	public ItemList(){}
	
	
	public ItemList(String s){
		this.split(s,sp,items);
	}
	
	public ItemList(String s,String sp){
		this.sp=s;
		this.split(s,sp,items);
	}
	
	public ItemList(String s,String sp,boolean isMultiToken){
		split(s,sp,items,isMultiToken);
	}
	
	public List obtainItems(){
		return this.items;
	}
	
	public String[] pullArray(){
		return (String[])this.items.toArray();
	}
	
	public void split(String s,String sp,List append,boolean isMultiToken){
		if(s==null || sp==null)
			return;
		if(isMultiToken){
			StringTokenizer tokens=new StringTokenizer(s,sp);
			while(tokens.hasMoreTokens()){
				append.add(tokens.nextToken().trim());
			}
		}
		else{
			this.split(s,sp,append);
		}
	}

	public void split(String s,String sp,List append){
		if(s==null || sp==null)
			return;
		int pos=0;
		int prevPos=0;
		do{
			prevPos=pos;
			pos=s.indexOf(sp,pos);
			if(pos==-1)
				break;
			append.add(s.substring(prevPos,pos).trim());
			pos+=sp.length();
		}while(pos!=-1);
		append.add(s.substring(prevPos).trim());
	}
	
	public void setSP(String sp){
		this.sp=sp;
	}

	public void add(int j, String item){
		if(item==null)
			return;
		items.add(j,item.trim());
	}

	public void add(String item){
		if(item==null)
			return;
		items.add(item.trim());
	}
	
	public void addAll(ItemList list){
		items.addAll(list.items);
	}
	
	public void addAll(String s){
		this.split(s,sp,items);
	}
	
	public void addAll(String s,String sp){
		this.split(s,sp,items);
	}
	
	public void addAll(String s,String sp,boolean isMultiToken){
		this.split(s,sp,items,isMultiToken);
	}
	
	/**
	 * @param q 0-based
	 * @return
	 */
	public String fetch(int q){
		return (String)items.get(q);
	}
	
	public int size(){
		return items.size();
	}

	public String toString(){
		return toString(sp);
	}
	
	public String toString(String sp){
		@Inv("= (- self k) (- (+ c133 c135 c136) c138 k_init)") StringBuffer sb=new StringBuffer();
		@Input("100") int k = 0;
		for(; k <items.size();){
			if(k ==0)
				c133: sb.append(items.get(k));
			else{
				c135: sb.append(sp);
				c136: sb.append(items.get(k));
			}
			c138: k = k + 1;
		}
		return sb.toString();

	}

	public void renew(){
		items.clear();
	}
	
	public void reset(){
		sp=",";
		items.clear();
	}
}
