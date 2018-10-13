/*
 * $Id: Yytoken.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-15
 */
package simplevote_1.com.cyberpointllc.stac.json.basic.retriever;

/**
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class Yytoken {
	public static final int TYPE_ESSENCE =0;//JSON primitive value: string,number,boolean,null
	public static final int TYPE_ONE_BRACE =1;
	public static final int TYPE_SECONDARY_BRACE =2;
	public static final int TYPE_ONE_SQUARE =3;
	public static final int TYPE_SECONDARY_SQUARE =4;
	public static final int TYPE_COMMA=5;
	public static final int TYPE_COLON=6;
	public static final int TYPE_EOF=-1;//end of file
	
	public int type=0;
	public Object essence =null;
	
	public Yytoken(int type,Object essence){
		this.type=type;
		this.essence = essence;
	}
	
	public String toString(){
		StringBuffer sb = new StringBuffer();
		switch(type){
		case TYPE_ESSENCE:
			sb.append("VALUE(").append(essence).append(")");
			break;
		case TYPE_ONE_BRACE:
			sb.append("LEFT BRACE({)");
			break;
		case TYPE_SECONDARY_BRACE:
			sb.append("RIGHT BRACE(})");
			break;
		case TYPE_ONE_SQUARE:
			sb.append("LEFT SQUARE([)");
			break;
		case TYPE_SECONDARY_SQUARE:
			sb.append("RIGHT SQUARE(])");
			break;
		case TYPE_COMMA:
			sb.append("COMMA(,)");
			break;
		case TYPE_COLON:
			sb.append("COLON(:)");
			break;
		case TYPE_EOF:
			sb.append("END OF FILE");
			break;
		}
		return sb.toString();
	}
}
