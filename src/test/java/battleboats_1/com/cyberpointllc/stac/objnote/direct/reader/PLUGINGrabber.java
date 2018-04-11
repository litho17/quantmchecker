/*
 * $Id: JSONParser.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-15
 */
package battleboats_1.com.cyberpointllc.stac.objnote.direct.reader;

import battleboats_1.com.cyberpointllc.stac.objnote.direct.PLUGINArray;
import battleboats_1.com.cyberpointllc.stac.objnote.direct.PLUGINObject;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;


/**
 * Parser for JSON text. Please note that JSONParser is NOT thread-safe.
 * 
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class PLUGINGrabber {
	public static final int S_INIT=0;
	public static final int S_IN_FINISHED_DETAIL =1;//string,number,boolean,null,object,array
	public static final int S_IN_OBJECT=2;
	public static final int S_IN_ARRAY=3;
	public static final int S_PASSED_PAIR_KEY=4;
	public static final int S_IN_PAIR_DETAIL =5;
	public static final int S_END=6;
	public static final int S_IN_ERROR=-1;
	
	private LinkedList managerStatusStack;
	private Yylex lexer = new Yylex((Reader)null);
	private Yytoken token = null;
	private int status = S_INIT;
	
	private int peekStatus(LinkedList statusStack){
		if(statusStack.size()==0)
			return -1;
		Integer status=(Integer)statusStack.getFirst();
		return status.intValue();
	}
	
    /**
     *  Reset the parser to the initial state without resetting the underlying reader.
     *
     */
    public void reset(){
        token = null;
        status = S_INIT;
        managerStatusStack = null;
    }
    
    /**
     * Reset the parser to the initial state with a new character reader.
     * 
     * @param in - The new character reader.
     * @throws IOException
     * @throws ParseDeviation
     */
	public void reset(Reader in){
		lexer.yyreset(in);
		reset();
	}
	
	/**
	 * @return The position of the beginning of the current token.
	 */
	public int pullPosition(){
		return lexer.takePosition();
	}
	
	public Object parse(String s) throws ParseDeviation {
		return parse(s, (ContainerFactory)null);
	}
	
	public Object parse(String s, ContainerFactory containerFactory) throws ParseDeviation {
		StringReader in=new StringReader(s);
		try{
			return parse(in, containerFactory);
		}
		catch(IOException ie){
			/*
			 * Actually it will never happen.
			 */
			throw new ParseDeviation(-1, ParseDeviation.ERROR_UNEXPECTED_DEVIATION, ie);
		}
	}
	
	public Object parse(Reader in) throws IOException, ParseDeviation {
		return parse(in, (ContainerFactory)null);
	}
	
	/**
	 * Parse JSON text into java object from the input source.
	 * 	
	 * @param in
     * @param containerFactory - Use this factory to createyour own JSON object and JSON array containers.
	 * @return Instance of the following:
	 *  org.json.simple.JSONObject,
	 * 	org.json.simple.JSONArray,
	 * 	java.lang.String,
	 * 	java.lang.Number,
	 * 	java.lang.Boolean,
	 * 	null
	 * 
	 * @throws IOException
	 * @throws ParseDeviation
	 */
	public Object parse(Reader in, ContainerFactory containerFactory) throws IOException, ParseDeviation {
		reset(in);
		LinkedList statusStack = new LinkedList();
		LinkedList detailStack = new LinkedList();
		
		try{
			do{
				followingToken();
				switch(status){
				case S_INIT:
					switch(token.type){
					case Yytoken.TYPE_DETAIL:
						status= S_IN_FINISHED_DETAIL;
						statusStack.addFirst(new Integer(status));
						detailStack.addFirst(token.detail);
						break;
					case Yytoken.TYPE_ONE_BRACE:
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						detailStack.addFirst(makeObjectContainer(containerFactory));
						break;
					case Yytoken.TYPE_ONE_SQUARE:
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						detailStack.addFirst(makeArrayContainer(containerFactory));
						break;
					default:
						status=S_IN_ERROR;
					}//inner switch
					break;
					
				case S_IN_FINISHED_DETAIL:
					if(token.type==Yytoken.TYPE_EOF)
						return detailStack.removeFirst();
					else
						throw new ParseDeviation(pullPosition(), ParseDeviation.ERROR_UNEXPECTED_TOKEN, token);
					
				case S_IN_OBJECT:
					switch(token.type){
					case Yytoken.TYPE_COMMA:
						break;
					case Yytoken.TYPE_DETAIL:
						if(token.detail instanceof String){
							String key=(String)token.detail;
							detailStack.addFirst(key);
							status=S_PASSED_PAIR_KEY;
							statusStack.addFirst(new Integer(status));
						}
						else{
							status=S_IN_ERROR;
						}
						break;
					case Yytoken.TYPE_SECONDARY_BRACE:
						if(detailStack.size()>1){
							statusStack.removeFirst();
							detailStack.removeFirst();
							status=peekStatus(statusStack);
						}
						else{
							status= S_IN_FINISHED_DETAIL;
						}
						break;
					default:
						status=S_IN_ERROR;
						break;
					}//inner switch
					break;
					
				case S_PASSED_PAIR_KEY:
					switch(token.type){
					case Yytoken.TYPE_COLON:
						break;
					case Yytoken.TYPE_DETAIL:
						statusStack.removeFirst();
						String key=(String) detailStack.removeFirst();
						Map parent=(Map) detailStack.getFirst();
						parent.put(key,token.detail);
						status=peekStatus(statusStack);
						break;
					case Yytoken.TYPE_ONE_SQUARE:
						statusStack.removeFirst();
						key=(String) detailStack.removeFirst();
						parent=(Map) detailStack.getFirst();
						List newArray= makeArrayContainer(containerFactory);
						parent.put(key,newArray);
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						detailStack.addFirst(newArray);
						break;
					case Yytoken.TYPE_ONE_BRACE:
						statusStack.removeFirst();
						key=(String) detailStack.removeFirst();
						parent=(Map) detailStack.getFirst();
						Map newObject= makeObjectContainer(containerFactory);
						parent.put(key,newObject);
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						detailStack.addFirst(newObject);
						break;
					default:
						status=S_IN_ERROR;
					}
					break;
					
				case S_IN_ARRAY:
					switch(token.type){
					case Yytoken.TYPE_COMMA:
						break;
					case Yytoken.TYPE_DETAIL:
						List val=(List) detailStack.getFirst();
						val.add(token.detail);
						break;
					case Yytoken.TYPE_SECONDARY_SQUARE:
						if(detailStack.size()>1){
							parseEngine(statusStack, detailStack);
						}
						else{
							status= S_IN_FINISHED_DETAIL;
						}
						break;
					case Yytoken.TYPE_ONE_BRACE:
						val=(List) detailStack.getFirst();
						Map newObject= makeObjectContainer(containerFactory);
						val.add(newObject);
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						detailStack.addFirst(newObject);
						break;
					case Yytoken.TYPE_ONE_SQUARE:
						val=(List) detailStack.getFirst();
						List newArray= makeArrayContainer(containerFactory);
						val.add(newArray);
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						detailStack.addFirst(newArray);
						break;
					default:
						status=S_IN_ERROR;
					}//inner switch
					break;
				case S_IN_ERROR:
					throw new ParseDeviation(pullPosition(), ParseDeviation.ERROR_UNEXPECTED_TOKEN, token);
				}//switch
				if(status==S_IN_ERROR){
					throw new ParseDeviation(pullPosition(), ParseDeviation.ERROR_UNEXPECTED_TOKEN, token);
				}
			}while(token.type!=Yytoken.TYPE_EOF);
		}
		catch(IOException ie){
			throw ie;
		}
		
		throw new ParseDeviation(pullPosition(), ParseDeviation.ERROR_UNEXPECTED_TOKEN, token);
	}

	private void parseEngine(LinkedList statusStack, LinkedList detailStack) {
		statusStack.removeFirst();
		detailStack.removeFirst();
		status=peekStatus(statusStack);
	}

	private void followingToken() throws ParseDeviation, IOException{
		token = lexer.yylex();
		if(token == null)
			token = new Yytoken(Yytoken.TYPE_EOF, null);
	}
	
	private Map makeObjectContainer(ContainerFactory containerFactory){
		if(containerFactory == null)
			return new PLUGINObject();
		Map m = containerFactory.makeObjectContainer();
		
		if(m == null)
			return new PLUGINObject();
		return m;
	}
	
	private List makeArrayContainer(ContainerFactory containerFactory){
		if(containerFactory == null)
			return new PLUGINArray();
		List l = containerFactory.creatArrayContainer();
		
		if(l == null)
			return new PLUGINArray();
		return l;
	}
	
	public void parse(String s, ContentManager contentManager) throws ParseDeviation {
		parse(s, contentManager, false);
	}
	
	public void parse(String s, ContentManager contentManager, boolean isResume) throws ParseDeviation {
		StringReader in=new StringReader(s);
		try{
			parse(in, contentManager, isResume);
		}
		catch(IOException ie){
			/*
			 * Actually it will never happen.
			 */
			throw new ParseDeviation(-1, ParseDeviation.ERROR_UNEXPECTED_DEVIATION, ie);
		}
	}
	
	public void parse(Reader in, ContentManager contentManager) throws IOException, ParseDeviation {
		parse(in, contentManager, false);
	}
	
	/**
	 * Stream processing of JSON text.
	 * 
	 * @see ContentManager
	 * 
	 * @param in
	 * @param contentManager
	 * @param isResume - Indicates if it continues previous parsing operation.
     *                   If set to true, resume parsing the old stream, and parameter 'in' will be ignored. 
	 *                   If this method is called for the first time in this instance, isResume will be ignored.
	 * 
	 * @throws IOException
	 * @throws ParseDeviation
	 */
	public void parse(Reader in, ContentManager contentManager, boolean isResume) throws IOException, ParseDeviation {
		if(!isResume){
			reset(in);
			managerStatusStack = new LinkedList();
		}
		else{
			if(managerStatusStack == null){
				isResume = false;
				reset(in);
				managerStatusStack = new LinkedList();
			}
		}
		
		LinkedList statusStack = managerStatusStack;
		
		try{
			do{
				switch(status){
				case S_INIT:
					contentManager.startPLUGIN();
					followingToken();
					switch(token.type){
					case Yytoken.TYPE_DETAIL:
						status= S_IN_FINISHED_DETAIL;
						statusStack.addFirst(new Integer(status));
						if(!contentManager.primitive(token.detail))
							return;
						break;
					case Yytoken.TYPE_ONE_BRACE:
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						if(!contentManager.startObject())
							return;
						break;
					case Yytoken.TYPE_ONE_SQUARE:
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						if(!contentManager.startArray())
							return;
						break;
					default:
						status=S_IN_ERROR;
					}//inner switch
					break;
					
				case S_IN_FINISHED_DETAIL:
					followingToken();
					if(token.type==Yytoken.TYPE_EOF){
						contentManager.endPLUGIN();
						status = S_END;
						return;
					}
					else{
						status = S_IN_ERROR;
						throw new ParseDeviation(pullPosition(), ParseDeviation.ERROR_UNEXPECTED_TOKEN, token);
					}
			
				case S_IN_OBJECT:
					followingToken();
					switch(token.type){
					case Yytoken.TYPE_COMMA:
						break;
					case Yytoken.TYPE_DETAIL:
						if(token.detail instanceof String){
							String key=(String)token.detail;
							status=S_PASSED_PAIR_KEY;
							statusStack.addFirst(new Integer(status));
							if(!contentManager.startObjectEntry(key))
								return;
						}
						else{
							status=S_IN_ERROR;
						}
						break;
					case Yytoken.TYPE_SECONDARY_BRACE:
						if(statusStack.size()>1){
							parseCoordinator(statusStack);
						}
						else{
							status= S_IN_FINISHED_DETAIL;
						}
						if(!contentManager.endObject())
							return;
						break;
					default:
						status=S_IN_ERROR;
						break;
					}//inner switch
					break;
					
				case S_PASSED_PAIR_KEY:
					followingToken();
					switch(token.type){
					case Yytoken.TYPE_COLON:
						break;
					case Yytoken.TYPE_DETAIL:
						statusStack.removeFirst();
						status=peekStatus(statusStack);
						if(!contentManager.primitive(token.detail))
							return;
						if(!contentManager.endObjectEntry())
							return;
						break;
					case Yytoken.TYPE_ONE_SQUARE:
						statusStack.removeFirst();
						statusStack.addFirst(new Integer(S_IN_PAIR_DETAIL));
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						if(!contentManager.startArray())
							return;
						break;
					case Yytoken.TYPE_ONE_BRACE:
						statusStack.removeFirst();
						statusStack.addFirst(new Integer(S_IN_PAIR_DETAIL));
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						if(!contentManager.startObject())
							return;
						break;
					default:
						status=S_IN_ERROR;
					}
					break;
				
				case S_IN_PAIR_DETAIL:
					/*
					 * S_IN_PAIR_VALUE is just a marker to indicate the end of an object entry, it doesn't proccess any token,
					 * therefore delay consuming token until next round.
					 */
					statusStack.removeFirst();
					status = peekStatus(statusStack);
					if(!contentManager.endObjectEntry())
						return;
					break;
					
				case S_IN_ARRAY:
					followingToken();
					switch(token.type){
					case Yytoken.TYPE_COMMA:
						break;
					case Yytoken.TYPE_DETAIL:
						if(!contentManager.primitive(token.detail))
							return;
						break;
					case Yytoken.TYPE_SECONDARY_SQUARE:
						if(statusStack.size()>1){
							statusStack.removeFirst();
							status=peekStatus(statusStack);
						}
						else{
							status= S_IN_FINISHED_DETAIL;
						}
						if(!contentManager.endArray())
							return;
						break;
					case Yytoken.TYPE_ONE_BRACE:
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						if(!contentManager.startObject())
							return;
						break;
					case Yytoken.TYPE_ONE_SQUARE:
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						if(!contentManager.startArray())
							return;
						break;
					default:
						status=S_IN_ERROR;
					}//inner switch
					break;
					
				case S_END:
					return;
					
				case S_IN_ERROR:
					throw new ParseDeviation(pullPosition(), ParseDeviation.ERROR_UNEXPECTED_TOKEN, token);
				}//switch
				if(status==S_IN_ERROR){
					throw new ParseDeviation(pullPosition(), ParseDeviation.ERROR_UNEXPECTED_TOKEN, token);
				}
			}while(token.type!=Yytoken.TYPE_EOF);
		}
		catch(IOException ie){
			status = S_IN_ERROR;
			throw ie;
		}
		catch(ParseDeviation pe){
			status = S_IN_ERROR;
			throw pe;
		}
		catch(RuntimeException re){
			status = S_IN_ERROR;
			throw re;
		}
		catch(Error e){
			status = S_IN_ERROR;
			throw e;
		}
		
		status = S_IN_ERROR;
		throw new ParseDeviation(pullPosition(), ParseDeviation.ERROR_UNEXPECTED_TOKEN, token);
	}

	private void parseCoordinator(LinkedList statusStack) {
		statusStack.removeFirst();
		status=peekStatus(statusStack);
	}
}
