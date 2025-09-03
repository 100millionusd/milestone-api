import { useState } from 'react';
import { getSession } from 'next-auth/react';
import { PrismaClient } from '@prisma/client';

const prisma = new PrismaClient();

export default function ProposalsPage({ initialProposals }) {
  const [proposals, setProposals] = useState(initialProposals);
  const [loading, setLoading] = useState({});

  const approveProposal = async (proposalId) => {
    setLoading(prev => ({ ...prev, [proposalId]: true }));
    
    try {
      const response = await fetch(`/api/proposals/${proposalId}/approve`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
      });

      if (response.ok) {
        const result = await response.json();
        alert(`Proposal approved! Project ID: ${result.projectId}`);
        
        // Remove approved proposal from list
        setProposals(prev => prev.filter(p => p.id !== proposalId));
      } else {
        const error = await response.json();
        throw new Error(error.error || 'Failed to approve proposal');
      }
    } catch (error) {
      console.error('Error:', error);
      alert(error.message || 'Error approving proposal');
    } finally {
      setLoading(prev => ({ ...prev, [proposalId]: false }));
    }
  };

  return (
    <div className="container mx-auto p-6">
      <h1 className="text-2xl font-bold mb-6">Proposals Management</h1>
      
      <div className="grid gap-4">
        {proposals.map((proposal) => (
          <div key={proposal.id} className="bg-white p-4 rounded-lg shadow">
            <h3 className="text-lg font-semibold">{proposal.title}</h3>
            <p className="text-gray-600">{proposal.description}</p>
            <p className="text-green-600 font-medium">Budget: ${proposal.budget}</p>
            <p className="text-blue-600">Client ID: {proposal.clientId}</p>
            <span className={`inline-block px-2 py-1 rounded text-sm ${
              proposal.status === 'PENDING' 
                ? 'bg-yellow-100 text-yellow-800' 
                : 'bg-green-100 text-green-800'
            }`}>
              Status: {proposal.status}
            </span>
            
            {proposal.status === 'PENDING' && (
              <button
                onClick={() => approveProposal(proposal.id)}
                disabled={loading[proposal.id]}
                className="mt-3 bg-green-600 text-white px-4 py-2 rounded hover:bg-green-700 disabled:opacity-50"
              >
                {loading[proposal.id] ? 'Approving...' : 'Approve Proposal'}
              </button>
            )}
          </div>
        ))}
      </div>
    </div>
  );
}

export async function getServerSideProps(context) {
  const session = await getSession(context);
  
  // Check if user is admin
  if (!session || session.user.role !== 'ADMIN') {
    return {
      redirect: {
        destination: '/login',
        permanent: false,
      },
    };
  }

  // Fetch pending proposals
  const proposals = await prisma.proposal.findMany({
    where: { status: 'PENDING' },
    orderBy: { createdAt: 'desc' }
  });

  return {
    props: {
      initialProposals: JSON.parse(JSON.stringify(proposals)),
    },
  };
}