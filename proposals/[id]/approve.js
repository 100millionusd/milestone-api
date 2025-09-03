import { getSession } from 'next-auth/react';
import { PrismaClient } from '@prisma/client';

const prisma = new PrismaClient();

export default async function handler(req, res) {
  if (req.method !== 'POST') {
    return res.status(405).json({ error: 'Method not allowed' });
  }

  try {
    // 1. Check authentication and admin role
    const session = await getSession({ req });
    if (!session || session.user.role !== 'ADMIN') {
      return res.status(401).json({ error: 'Unauthorized' });
    }

    const { id } = req.query;

    // 2. Get the proposal
    const proposal = await prisma.proposal.findUnique({
      where: { id },
    });

    if (!proposal) {
      return res.status(404).json({ error: 'Proposal not found' });
    }

    if (proposal.status === 'APPROVED') {
      return res.status(400).json({ error: 'Proposal already approved' });
    }

    // 3. Update proposal status to APPROVED
    await prisma.proposal.update({
      where: { id },
      data: { 
        status: 'APPROVED',
        updatedAt: new Date()
      }
    });

    // 4. Create a new project from the proposal
    const project = await prisma.project.create({
      data: {
        title: proposal.title || `Project from Proposal ${id.substring(0, 8)}`,
        description: proposal.description,
        budget: proposal.budget || 0,
        clientId: proposal.clientId,
        vendorId: proposal.vendorId,
        proposalId: id,
        status: 'ACTIVE'
      }
    });

    // 5. Link project back to proposal
    await prisma.proposal.update({
      where: { id },
      data: { projectId: project.id }
    });

    res.status(200).json({ 
      success: true, 
      projectId: project.id,
      message: 'Proposal approved and project created successfully'
    });

  } catch (error) {
    console.error('Error approving proposal:', error);
    res.status(500).json({ error: 'Internal server error' });
  }
}