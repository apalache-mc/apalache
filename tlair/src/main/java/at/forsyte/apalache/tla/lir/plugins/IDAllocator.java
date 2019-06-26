package at.forsyte.apalache.tla.lir.plugins;

import java.util.Map;
import java.util.HashMap;
import java.util.Vector;

/**
 * Created by jkukovec on 11/28/16.
 *
 * TODO: do we still need it?
 */
public class IDAllocator<ValType> {
    protected Vector<ValType> m_ID_to_Val;
    protected Map<ValType,Integer> m_Val_to_ID;

    public IDAllocator(){
        m_ID_to_Val = new Vector<>();
        m_Val_to_ID = new HashMap<>();
    }

    public int predict( ValType p_new ){
        if( m_Val_to_ID.containsKey( p_new ) ) {
            return m_Val_to_ID.get( p_new );
        }
        else return m_ID_to_Val.size();
    }

    public int allocate( ValType p_new ) {
        if( m_Val_to_ID.containsKey( p_new ) ) {
            return m_Val_to_ID.get( p_new );
        }
        else{
            int s = m_ID_to_Val.size();
            m_Val_to_ID.put( p_new, s );
            m_ID_to_Val.add( p_new );
            return s;
        }
    }

    public Vector<ValType> keys(){
        return m_ID_to_Val;
    }

    public int getID( ValType p_val ){
        if( m_Val_to_ID.containsKey( p_val ) ) return m_Val_to_ID.get( p_val );
        return -1; // -1 if not allocated.
    }

    public ValType getVal( int p_ID ){
        if( p_ID < 0 || p_ID >= m_ID_to_Val.size() ) return null;
        return m_ID_to_Val.get( p_ID );
    }

    public int nextID(){
        return m_ID_to_Val.size();
    }

    public void reset() {
        m_ID_to_Val.clear();
        m_Val_to_ID.clear();
    }
}
