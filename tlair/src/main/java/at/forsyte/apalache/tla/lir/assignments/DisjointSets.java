package at.forsyte.apalache.tla.lir.assignments;

import java.util.*;

/**
 * Created by jkukovec on 08/23/17.
 */
public class DisjointSets<ValType> {
    // TODO: move it to tla-assignments (Igor)
    private Map<ValType,ValType> m_parent;
    private Map<ValType,Integer> m_rank;

    public DisjointSets(){
        m_parent = new HashMap<>();
        m_rank   = new HashMap<>();
    }

    public boolean contains( ValType p_el ){
        return m_parent.containsKey( p_el );
    }

    public Set<ValType> allElements(){
        return m_parent.keySet();
    }

    public List<Set<ValType>> allSets(){
        Map< ValType, Set<ValType > > sets = new HashMap<>();
        for ( ValType entry : m_parent.keySet()){
            ValType root = find(entry);
            Set<ValType> newset = sets.getOrDefault( root, new HashSet<>() );
            newset.add( entry );
            sets.put( root, newset );
        }
        return new LinkedList<>( sets.values() );
    }

    public void make( ValType p_el ){
        if( ! m_parent.containsKey( p_el ) ){
            m_parent.put( p_el, p_el );
            m_rank.put( p_el, 0 );
        }

    }

    public ValType find( ValType p_el ){
        // assume x actually in the map
        ValType parent = m_parent.get( p_el );
        if( parent != p_el ){
            m_parent.put( p_el, find( parent ) );
        }
        return m_parent.get( p_el );
    }

    public void union( ValType p_elX, ValType p_elY ){
        ValType xRoot = find( p_elX );
        ValType yRoot = find( p_elY );

        if( xRoot == yRoot ) return;

        Integer rX = m_rank.get( xRoot );
        Integer rY = m_rank.get( yRoot );

        if ( rX < rY ) {
            m_parent.put( xRoot, yRoot );
        }
        else if ( rX > rY ) {
            m_parent.put( yRoot, xRoot );
        }
        else {
            m_parent.put( yRoot, xRoot );
            m_rank.put( xRoot, rX + 1 );
        }
    }


}
